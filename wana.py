#!/usr/bin/python3
# -*- coding: utf-8 -*-
"""
The module is the main entry of Wana analysis tool. It consists of a class and
some functions. 
"""
import argparse
import os
import re
import typing
import z3
import traceback
from typing import List
from func_timeout import func_timeout
from func_timeout import FunctionTimedOut
import time 

import bin_format
import sym_exec
import logger
import structure
import utils
from global_variables import global_vars
from runtime import WasmFunc
from bug_analyzer import locate_transfer, function_analysis, build_model,detect_permissions,get_best_tx, symbolic_loop
from bug_analyzer import fake_eos_analysis
from bug_analyzer import count_instruction
from emulator import hostfunc_map


class Runtime:
    """A webassembly runtime manages Store, Stack, and other structures.
    They forming the WebAssembly abstract.

    Attributes:
        module: constructed by reading WASM file and simply store the content.
        module_instance: the truly runtime instance, store pointers of function, 
                         memory and etc of module.
        store: for simplification, the store contains some frequently used information.
    """

    # @profile
    def reinit(self):
        global_vars.re_init()
        sym_exec.init_variables()
        self.__init__(self.module)

    def __init__(self, module: structure.Module, imps: typing.Dict = None):
        """Initilize Runtime object.

        Args:
            module: constructed by reading WASM file and simply store the content.
            imps: a dict, the key is the import name and the value is the pointer

        Returns:
            Runtime: instance of Runtime class.
        """
        self.module = module
        self.module_instance = sym_exec.ModuleInstance()
        self.store = sym_exec.Store()

        imps = imps if imps else {}
        externvals = []
        for e in self.module.imports:
            if e.kind == bin_format.extern_func:
                # The two if branch is used to detect the possibility of random vulnerability.
                # If the "tapos_block_num" is called while "send_inline"/"send_deferred" is related
                # and called, it could be considered a bug.
                e.name=e.name.strip('_')
                if ((e.module in ('env',) and e.name in ('tapos_block_num', 'tapos_block_prefix'))
                        or (e.module in ('ethereum',) and e.name in ('getBlockNumber', 'getBlockHash', 'getBlockTimestamp'))):
                    global_vars.add_tapos_block_function_addr(len(self.store.funcs))
                if (e.module in ('env',) and e.name in ('send_inline', 'send_deferred')
                        or e.module in ('ethereum',) and e.name in ('call',)):  # current version does not include 'callCode', 'callDelegate', 'callStatic'
                    global_vars.add_send_token_function_addr(len(self.store.funcs))#addr其实就是store.funcs的索引
                if e.module in ('env',) and e.name in ('eosio_assert',):
                    global_vars.eosio_assert_addrs.add(len(self.store.funcs))
                if e.module in ('env',) and e.name in ('action_data_size',):
                    global_vars.action_data_size_addrs.add(len(self.store.funcs))
                if e.module in ('env',) and e.name in ('read_action_data',):
                    global_vars.read_action_data_addrs.add(len(self.store.funcs))
                if e.module in ('ethereum',) and e.name in ('callDelegate',):
                    global_vars.add_call_delegate_addr(len(self.store.funcs))
                if e.module in ('ethereum',) and e.name in ('getCallValue',):
                    global_vars.add_get_call_value_addr(len(self.store.funcs))
                if e.module in ('ethereum',) and e.name in ('revert',):
                    global_vars.add_revert_addr(len(self.store.funcs))
                #这里的hostfunc就是eosio中的库函数，传入并存储了函数类型，库函数模拟时具体要运行的代码，和函数名
                a = sym_exec.HostFunc(self.module.types[e.desc], hostfunc_map[e.module][e.name], e.name)
                if 'db' in e.name and 'store' in e.name:
                    global_vars.db_store_id=len(self.store.funcs)
                if 'db' in e.name and 'update' in e.name:
                    global_vars.db_udpate_id=len(self.store.funcs)
                if 'db' in e.name and 'remove' in e.name:
                    global_vars.db_remove_id=len(self.store.funcs)
                self.store.funcs.append(a)
                externvals.append(sym_exec.ExternValue(e.kind, len(self.store.funcs) - 1))
                continue
            if e.kind == bin_format.extern_table:
                a = None
                self.store.tables.append(a)
                externvals.append(sym_exec.ExternValue(e.kind, len(self.store.tables) - 1))
                continue
            if e.kind == bin_format.extern_mem:
                a = None
                self.store.mems.append(a)
                self.store.smems.append(a)
                externvals.append(sym_exec.ExternValue(e.kind, len(self.store.mems) - 1))
                continue
            if e.kind == bin_format.extern_global:
                a = sym_exec.GlobalInstance(sym_exec.Value(e.desc.valtype, None), e.desc.mut)
                self.store.globals.append(a)
                externvals.append(sym_exec.ExternValue(e.kind, len(self.store.globals) - 1))
                continue
        self.module_instance.instantiate(self.module, self.store, externvals)

    def func_addr(self, name: str):
        """Search the address of export function.

        Args:
            name: the name of function.

        Returns:
            address: the address in module instance.
        """
        # Get a function address denoted by the function name.
        for e in self.module_instance.exports:
            if e.name == name and e.value.extern_type == bin_format.extern_func:
                return e.value.addr
        raise Exception('Function not found!')


    def exec(self, name: str, args: typing.List):
        """Execute the export function.

        Args:
            name: the export function name.
            args: the parameters of function.

        Returns:
            r: the result of execution of function and args.
        """
        # Invoke a function denoted by the function address with the provided arguments.
        func_addr = self.func_addr(name)
        logger.infoln(f'Running function {name}):')
        r = self.exec_by_address(func_addr, args)
        if r:
            return r
        return None

    def exec_by_index(self, table_index: int, args: typing.List, init_constraints: typing.List = ()):
        """Executing a function depends on its address.

        Args:
            init_constraints:
            table_index: function index in table.
            args: the parameters.

        Returns:
            r: the result.
        """
        module = self.module_instance
        table = self.store.tables[module.tableaddrs[0]]
        address = table.elem[table_index]
        return self.exec_by_address(address, args, init_constraints)

    # @profile
    def exec_by_address(self, address: int, args: typing.List, init_constraints: typing.List = ()):
        """Executing a function depends on its address.

        Args:
            address: the address of function of store.
            args: the parameters.
            init_constraints: initial constraints for symbolic execution.

        Returns:
            r: the result.
        """
        # Invoke a function denoted by the function address with the provided arguments.
        func = self.store.funcs[self.module_instance.funcaddrs[address]]

        if not isinstance(func, WasmFunc):
            return None

        # Mapping check for Python val-type to WebAssembly val-type.
        for i, e in enumerate(func.functype.args):
            if e in [bin_format.i32, bin_format.i64]:
                assert isinstance(args[i], int) or isinstance(args[i], z3.BitVecRef)

            if e in [bin_format.f32, bin_format.f64]:
                assert isinstance(args[i], float) or isinstance(args[i], z3.FPRef)

            args[i] = sym_exec.Value(e, args[i])#对于每个值给了类型
        stack = sym_exec.Stack()
        stack.ext(args)#将参数放到了栈顶
        self.store.visited=[]
        logger.infoln(f'Running function address {address}({", ".join([str(e) for e in args])}):')
        r = sym_exec.call(self.module_instance, address, self.store, stack, init_constraints)
        if r:
            return r
        return None

    def exec_a_func(self,func_id:int)->None:
        """给定名字，执行一个函数
        """
        # global_vars.output.write(f"func id:{func_id}\n")
        print(self.exec_by_address(func_id,self._get_symbolic_params(func_id)))



    def exec_all_func(self) -> None:
        """Executing all functions of the module.
        """
        for e in self.module_instance.exports:
            logger.infoln(e.name, e.value.addr)
            if e.value.extern_type == bin_format.extern_func:
                try:
                    self.exec_by_address(e.value.addr, self._get_symbolic_params(e.value.addr))
                except AttributeError as e:
                    logger.println('AttributeError found: ', e)
                except z3.z3types.Z3Exception as e:
                    logger.println('z3 BitVec format exception:, ', e)
                except Exception as e:
                    logger.println('Undefined error: ', e)

    def _get_symbolic_params(self, address: int):
        """Create the valid symbolic parameters of corresponding function.

        Args:
            address: function address.

        Returns:
            symbolic_params: a list of ordered symbolic parameters.
        """
        # Invoke a function denoted by the function address with the provided arguments.
        func = self.store.funcs[self.module_instance.funcaddrs[address]]
        return utils.gen_symbolic_args(func)


def load(name: str, imps: typing.Dict = None) -> Runtime:
    #load的第二个参数从没被用过
    """The function reads a file and constructs a Runtime instance.

    Args:
        name: the path of WASM file.
        imps: the import function, memory and etc.

    Returns:
        runtime: Runtime instance.
    """
    with open(name, 'rb') as f:
        module = structure.Module.from_reader(f)#module是wasm文件的一个module的静态分析对象,这里就将文件载入到了内存中了,成为了一个对象
    global_vars.re_init()#global_vars保存的是符号执行过程中要用到的值
    sym_exec.init_variables()
    return Runtime(module, imps)


def list_wasm_in_dir(path: str) -> List[str]:
    """Find all WASM file of a directory.

    Args:
        path: the path of directory.

    Returns:
        wasm_files: a list of path of WASM file.
    """
    wasm_files = []
    file_list = os.listdir(path)
    for file_name in file_list:
        current_path = os.path.join(path, file_name)
        if os.path.isdir(current_path):
            wasm_files.extend(list_wasm_in_dir(current_path))
        else:
            wasm_files.append(current_path)
    return [wasm_file for wasm_file in wasm_files if re.match(r'.*\.wasm', wasm_file) is not None]


def parse_arguments():
    """Parse the arguments of wana.py and execute corresponding function.

    Returns:
        args: the arguments.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-wt',
        '--wast',
        action='store_true',
        help='Check WAST format file'
    )
    parser.add_argument(
        '-wm',
        '--wasm',
        action='store_true',
        help='Check WASM format file'
    )
    parser.add_argument(
        '-e',
        '--execute',
        type=str,
        help='Execute a smart contract'
    )
    parser.add_argument(
        '-a',
        '--analyse-directory',
        type=str,
        help='Execute every wasm file in the directory'
    )
    parser.add_argument(
        '-c',
        '--count-instruction',
        action='store_true',
        help='Count the number of some type of instruction'
    )
    parser.add_argument(
        '-v',
        '--version',
        action='version',
        version='wana version 0.9.0 - buaa-scse-les'
    )
    parser.add_argument(
        '-t',
        '--timeout',
        help='Timeout for analysis using z3 in ms.',
        type=int,
        default=2000
    )
    parser.add_argument(
        '-s',
        '--sol',
        action='store_true',
        help='Analyze the solidity smart contract'
    )
    parser.add_argument(
        '-l',
        '--lvl',
        type = int,
        default=0,
        help='logger.lvl'
    )
    parser.add_argument(
        '--simple',
        action='store_true',
        help='simple execute wasm'
    )
    parser.add_argument(
        '-o',
        '--output',
        type=str,
        help='output file name'
    )
    parser.add_argument(
        '-td',
        '--temp_dir',
        type=str,
        help='temp dir'
    )
    return parser.parse_args()


def main():
    """The main function of analysis. It executes static analysis and symbolic execution.
    The result will be stored in result.txt of project directory."""

    args = parse_arguments()

    # Compile
    if args.sol:
        global_vars.contract_type = 'ethereum'

    if args.lvl:
        logger.lvl = global_vars.lvl = args.lvl

    if args.simple:
        global_vars.is_simple = args.simple

    if args.output:
        global_vars.output_file = open(args.output,"w")

    if args.temp_dir:
        global_vars.pathOfHookedContract= args.temp_dir
        # global_vars.pathOfHookedContract= args.temp_dir if args.temp_dir[-1]=='\\' else args.temp_dir+'\\'
    start = float()
    end = float()
    # Execute a export functions of wasm
    if args.execute:
        try:
            start = time.perf_counter()
            func_timeout(args.timeout, execution_and_analyze, args=(args.execute,))
            end = time.perf_counter()
        except FunctionTimedOut:
            logger.println(f'{args.execute}: time out')
            end = time.perf_counter()
            global_vars.output_file.close()
        except Exception as e:
            logger.infoln(traceback.format_exc())
            logger.println(f'Error: {e}')

    # Execute all export functions of wasm
    if args.analyse_directory:
        wasm_files = list_wasm_in_dir(args.analyse_directory)
        for contract_path in wasm_files:
            try:
                func_timeout(args.timeout, execution_and_analyze, args=(contract_path,))
            except FunctionTimedOut:
                logger.println(f'{contract_path}: time out')
            except Exception as e:
                logger.infoln(traceback.format_exc())
                logger.println(f'Error: {e}')

    # Count the number of instruction
    if args.count_instruction:
        wasm_files = list_wasm_in_dir(args.count_instruction)
        for file_name in wasm_files:
            logger.println('Count instruction of contract: ', os.path.basename(file_name))
            try:
                vm = load(file_name)
            except Exception as e:
                logger.println(f'failed initialization: {e}')
                continue
            float_count, count = count_instruction(vm.module.funcs)
            logger.println(f'float: {float_count}  all: {count}')

    logger.println(f'use time: {end-start}')


def execution_and_analyze(contract_path):
    #符号分析开始的函数
    name = os.path.basename(contract_path).split('.wasm')[0]
    user_name=name.split('_')[-1] if '_' in name else name
    print("name",name)
    try:
        #global_vars.output_before()
        global_vars.vm = vm = load(contract_path)
    except Exception as e:
        logger.println(f'{e}: [{name}] failed initialization')
        traceback.print_exc()
        return
    try:
        global_vars.set_name_int64(user_name)
    except Exception as e:
        logger.infoln(f'invalid contract name {name}: {e}')

    try:
        # before_sym_exec(vm, name)
        global_vars.func_name_stack=[]
        # if global_vars.transfer_function_index:
        #     vm.exec_by_index(global_vars.transfer_function_index,global_vars.transfer_function_params)
        # if global_vars.transfer_function_address:
        #     vm.exec_by_address(global_vars.transfer_function_address,global_vars.transfer_function_params)

        #second work
        global_vars.should_write_rule=False
        data_dir = '/'.join(contract_path.split('/')[:-2])
        symbolic_loop(vm,name,data_dir)

        # # first work
        # global_vars.should_write_rule=True
        # build_model(vm,name)

        # detect_permissions(vm, name)
        # vm.exec_a_func(32)
        # get_best_tx(vm,name)

        # res=[]
        # while True:
        #     r=get_best_tx(vm,name)
        #     if r is None:
        #         break
        #     res.append(r)
        after_sym_exec(name)#打印全局变量中存储的结果
    except Exception as e:
        logger.println(f'Error: {e}')
        traceback.print_exc()
    finally:
        global_vars.clear_count()


def before_sym_exec(vm, name):
    locate_transfer(vm, name)#将特殊参数传入apply函数开始执行,如果最后能够执行到call_indirect函数的话,就看作有处理transfer,表项地址放在global_vars.transfer_function_index里
    # function_analysis(vm)#对以太坊的合约才进行操作


def after_sym_exec(name):
    print("after_sym_exec")
    os.system(f"rm -rf {global_vars.pathOfHookedContract}")
    #print(global_vars)
    #global_vars.output_after()
    if global_vars.fake_eos_transfer_count > 0:
        logger.println(f'{name}: fake eos found')
    if global_vars.forged_transfer_notification_count > 0:
        logger.println(f'{name}: forged transfer notification found')
    if global_vars.block_dependency_count > 0:
        logger.println(f'{name}: dependency found')
    if global_vars.ethereum_delegate_call > 0:
        logger.println(f'{name}: delegate call found')
    if global_vars.ethereum_greedy > 0:
        logger.println(f'{name}: greedy found')
    if len(global_vars.call_symbolic_ret) > 0:
        logger.println(f'{name}: mishandled exception found')
    if global_vars.ethereum_reentrancy_detection > 0:
        logger.println(f'{name}: reentrancy found')
    if global_vars.missing_permissions:
        logger.println(f'{name}: missing permissions found')
    if global_vars.rollback:
        logger.println(f'{name}: rollback found')
    if global_vars.overflow_vul:
        logger.println(f'{name}: overflow found')
    if global_vars.block_information_depend:
        logger.println(f'{name}: block information dependency found')

if __name__ == '__main__':
    main()
