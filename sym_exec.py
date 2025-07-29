# !/usr/bin/python3
# -*- coding: utf-8 -*-
"""
The main logic of symbolic execution. Apart from the execution logic, the module
contains some variables to help execution, some class to construct runtime structure.
"""
import math
import z3
import copy
import utils
import traceback
from random import randint, uniform
from z3.z3util import get_vars
from collections import defaultdict
import sys

import emulator
import logger
import number
from global_variables import global_vars
from bug_analyzer import check_block_dependence_old
from bug_analyzer import check_ethereum_delegate_call
from bug_analyzer import check_ethereum_greedy
from bug_analyzer import cur_state_analysis
from bug_analyzer import check_mishandled_exception
from runtime import *
from bug_analyzer import library_function_dict
from bug_analyzer import find_symbolic_in_solver
from global_state import GlobalState
import pprint
# from memory_profiler import profile



# The variables will be used in exec() function.
path_condition = []#路径约束集合，可能有用
# memory_address_symbolic_variable = {}
solver = z3.Solver()
recur_depth = 0
loop_depth_dict = defaultdict(int)
# path_abort = False
path_depth = 0
block_number_flag = False
gas_cost = 0
func_cnt = 0
rule_cnt = 0
call_cnt = 0
gvar_cnt=0
primise=[]
action=[]
conclusion=[]
next_vars=None

class ModuleInstance:
    """A module instance is the runtime representation of a module. It is created by instantiating a module, and
    collects runtime representations of all entities that are imported, defined, or exported by the module.

    moduleinst ::= {
        types functype∗
        funcaddrs funcaddr∗
        tableaddrs tableaddr∗
        memaddrs memaddr∗
        globaladdrs globaladdr∗
        exports exportinst∗
    }

    Attributes:
        types: list of function type
        funcaddrs: function address of current module
        tableaddrs: table address of current module
        globaladdrs: global address of current module
        exports: the export instance of current module
    """

    def __init__(self):
        self.types: typing.List[structure.FunctionType] = []
        self.funcaddrs: typing.List[int] = []
        self.tableaddrs: typing.List[int] = []
        self.memaddrs: typing.List[int] = []
        self.globaladdrs: typing.List[int] = []
        self.exports: typing.List[ExportInstance] = []

    def instantiate(
            self,
            module: structure.Module,
            store: Store,
            externvals: typing.List[ExternValue] = None
    ):
        global gvar_cnt
        self.types = module.types
        # [TODO] : z3.If module is not valid, the panic
        for e in module.imports:
            assert e.kind in bin_format.extern_type

        assert len(module.imports) == len(externvals)

        for i in range(len(externvals)):
            e = externvals[i]
            assert e.extern_type in bin_format.extern_type
            if e.extern_type == bin_format.extern_func:
                a = store.funcs[e.addr]
                b = self.types[module.imports[i].desc]
                assert a.functype.args == b.args
                assert a.functype.rets == b.rets
            elif e.extern_type == bin_format.extern_table:
                a = store.tables[e.addr]
                b = module.imports[i].desc
                assert a.elemtype == b.elemtype
                assert import_matching_limits(b.limits, a.limits)
            elif e.extern_type == bin_format.extern_mem:
                a = store.mems[e.addr]
                b = module.imports[i].desc
                assert import_matching_limits(b, a.limits)
            elif e.extern_type == bin_format.extern_global:
                a = store.globals[e.addr]
                b = module.imports[i].desc
                assert a.value.valtype == b.valtype
        # Let vals be the vector of global initialization values determined by module and externvaln
        auxmod = ModuleInstance()
        auxmod.globaladdrs = [e.addr for e in externvals if e.extern_type == bin_format.extern_global]
        stack = Stack()
        frame = Frame(auxmod, [], 1, -1)
        stack.add(frame)
        vals = []
        #初始规则
        global_vars.should_write_rule=True
        #primise=[]
        #conclusion=[gen_gvars([],len(module.globals),gvar_cnt)]
        #write_rule(primise,["Init0()"],conclusion)
        global_vars.should_write_rule=False
        print("globals init")
        for i,glob in enumerate(module.globals):#globals: list of global object
            print("exec globals ",i,glob.expr)
            v = exec_expr(store, frame, stack, glob.expr, -1)[0][0]#对于global object进行了执行
            print(v)
            # global_vars.should_write_rule=True
            # primise=[gen_gvars([],len(module.globals),gvar_cnt)]
            vals.append(v)
            # #primise.append(f"SubstVar(compglobalX{i},{v})")
            # gvar_cnt+=1
            # conclusion=[gen_gvars([],len(module.globals),gvar_cnt)]
            # #write_rule(primise,[],conclusion)
            # global_vars.should_write_rule=False
        assert isinstance(stack.pop(), Frame)

        # Allocation
        self.allocate(module, store, externvals, vals)

        # Push the frame F to the stack
        frame = Frame(self, [], 1, -1)
        stack.add(frame)
        # For each element segment in module.elem, then do:
        for e in module.elem:
            offset = exec_expr(store, frame, stack, e.expr, -1)[0][0]
            assert offset.valtype == bin_format.i32
            t = store.tables[self.tableaddrs[e.tableidx]]
            for i, elem in enumerate(e.init):
                t.elem[offset.n + i] = elem
        # For each data segment in module.data, then do:
        for e in module.data:
            offset = exec_expr(store, frame, stack, e.expr, -1)[0][0]
            assert offset.valtype == bin_format.i32
            m = store.mems[self.memaddrs[e.memidx]]
            end = offset.n + len(e.init)
            assert end <= len(m.data)
            global_vars.should_write_rule=True
            #primise=[gen_gvars(store.mems[self.memaddrs[e.memidx]].data,len(module.globals),gvar_cnt)]
            # for i in range(len(e.init)):
                #primise.append(f"SubstVar8(compmemoryX{offset.n+i},{e.init[i]})")
            m.data[offset.n: offset.n + len(e.init)] = e.init
            gvar_cnt+=1
            #conclusion=[gen_gvars(store.mems[self.memaddrs[e.memidx]].data,len(module.globals),gvar_cnt)]
            #write_rule(primise,[],conclusion)
            global_vars.should_write_rule=False
            # store the abi name and its address
            global_vars.data_addr_dict[offset.n] = e.init.decode(errors='ignore').split('\00')[0]
        # Assert: due to validation, the frame F is now on the top of the stack.
        assert isinstance(stack.pop(), Frame)
        assert stack.len() == 0
        # z3.If the start function module.start is not empty, invoke the function instance.
        if module.start:
            logger.infoln(f'running start function {module.start}:')
            call(self, module.start, store, stack)

    def allocate(
            self,
            module: structure.Module,
            store: Store,
            externvals: typing.List[ExternValue],
            vals: typing.List[Value]
    ):
        self.types = module.types
        # Imports
        self.funcaddrs.extend([e.addr for e in externvals if e.extern_type == bin_format.extern_func])
        self.tableaddrs.extend([e.addr for e in externvals if e.extern_type == bin_format.extern_table])
        self.memaddrs.extend([e.addr for e in externvals if e.extern_type == bin_format.extern_mem])
        self.globaladdrs.extend([e.addr for e in externvals if e.extern_type == bin_format.extern_global])
        # For each function func in module.funcs, then do:
        for func in module.funcs:
            functype = self.types[func.typeidx]
            funcinst = WasmFunc(functype, self, func)
            store.funcs.append(funcinst)
            self.funcaddrs.append(len(store.funcs) - 1)
        # For each table in module.tables, then do:
        for table in module.tables:
            tabletype = table.tabletype
            elemtype = tabletype.elemtype
            tableinst = TableInstance(elemtype, tabletype.limits)
            store.tables.append(tableinst)
            self.tableaddrs.append(len(store.tables) - 1)
        # For each memory module.mems, then do:
        for mem in module.mems:
            meminst = MemoryInstance(mem.memtype)
            store.mems.append(meminst)
            store.smems.append(SymbolicMemoryInstance())
            self.memaddrs.append(len(store.mems) - 1)
        # For each global in module.globals, then do:
        for i, glob in enumerate(module.globals):
            val = vals[i]
            if val.valtype != glob.globaltype.valtype:
                raise Exception('Mimatch valtype!')
            globalinst = GlobalInstance(val, glob.globaltype.mut)
            store.globals.append(globalinst)
            self.globaladdrs.append(len(store.globals) - 1)
        # For each export in module.exports, then do:
        for i, export in enumerate(module.exports):
            externval = ExternValue(export.kind, export.desc)
            exportinst = ExportInstance(export.name, externval)
            # set address of functions
            if export.name == 'apply' and export.kind == bin_format.extern_func:
                logger.infoln('apply address:', export.desc)
                global_vars.set_apply_function_addr(externval.addr)
            if export.name == 'main' and export.kind == bin_format.extern_func:
                logger.infoln('main address:', export.desc)
                global_vars.set_main_function_addr(externval.addr)
            self.exports.append(exportinst)


def import_matching_limits(limits1: structure.Limits, limits2: structure.Limits):
    """Check the limits is valid or not.

    Args:
        limits1: a limit instance
        limits2: a limit instance

    Returns:
        true if the limit is valid else false.
    """
    min1 = limits1.minimum
    max1 = limits1.maximum
    min2 = limits2.minimum
    max2 = limits2.maximum
    if max2 is None or (max1 is not None and max1 <= max2):
        return True
    return False


def hostfunc_call(
        _: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack
):
    """The function call lib function. It will pop the args from stack
    and return the result.

    Args:
        _: deprecated parameter.
        address: the address of function.
        store: store the functions.
        stack: the current stack.

    Returns:
        result: the list of result, only one elem.
    """
    f: HostFunc = store.funcs[address]

    valn = [stack.pop() for _ in f.functype.args][::-1]
    ctx = Ctx(store.mems)
    r = f.hostcode(ctx, *[e.n for e in valn])
    return [Value(f.functype.rets[0], r)],[GlobalState()]


# @profile
def fake_hostfunc_call(
        module_instance: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack,
        memory: list
):  
    """When the lib function is not exist, the hostfunc_call will crash, so the
    fake_hostfunc_call is useful because the analysis tool could not get the lib
    function.

    Args:
        _: deprecated parameter.
        address: the address of function.
        store: store the functions.
        stack: the current stack.

    Returns:
        result: the list of result, only one elem.
    """
    f: HostFunc = store.funcs[address]
    valn = [stack.pop() for _ in f.functype.args][::-1]
    val0 = []
    action=[]
    #sensitive_operation=["db_update_i64","db_store_i64","db_idx64_update","db_idx64_store","db_idx64_remove","db_remove_i64","send_inline","require_recipient","send_context_free_inline"]
    sensitive_operation = ['send_inline']#, 'send_deferred', 'send_context_free_inline', 'cancel_deferred'] 
                # 'db_find_i64', 'db_lowerbound_i64', 'db_get_i64',
                # 'db_update_i64', 'db_store_i64', 'db_remove_i64', 'db_idx64_store', 'db_idx64_update', 'db_idx64_remove', 'db_idx128_update',
                # 'db_idx128_store', 'db_idx128_remove', 'db_idx256_remove', 'db_idx256_store']
    send_operation=["send_inline","send_context_free_inline"]
    authenticate_operation=["require_auth","require_auth2","has_auth"]
    state=[GlobalState()]
    if f.funcname:
        if f.funcname in sensitive_operation:
            action.append("SensitiveOp()")
            if not global_vars.call_authenticate:
                global_vars.missing_permissions=True
                print("missing permission checking vulneralbility find")
            if global_vars.get_block_state or global_vars.call_block_state :
                global_vars.block_information_depend=True
                print("block info depend vulneralbility find")
            if global_vars.overflow:
                global_vars.overflow_vul=True
                print("overflow vulnerabiliy find")
            global_vars.sensitive_op=True
        if f.funcname in authenticate_operation:
            action.append("Authenticate()")
            global_vars.call_authenticate=True
        if f.funcname in send_operation:
            action.append("Send()")
            if not global_vars.call_block_state:
                global_vars.rollback=True
            print("rollback vulneralbility find")
        # if "db" in f.funcname and ("find" in f.funcname or "get" in f.funcname):
        if f.funcname in ["tapos_block_num","tapos_block_prefix"]:
            action.append("Get_Block_State()")
            print("get block state")
            global_vars.get_block_state=True
            if global_vars.sensitive_op:
                global_vars.block_information_depend=True
            print("block info depend vulneralbility find")
        logger.infoln(f'call eth.hostfunc : {f.funcname} {address}')
    if f.funcname in emulator.realize_list_wasm:#如果库函数已经被实现了
        # [TODO] Pass different parameters according to the situation
        r=f.hostcode(valn, solver, store, module_instance)
        if len(f.functype.rets)<=0 :
            return [],r[1],action
        if  r is None:
            return [],state,action
        for c in r[1][0].constraints:
            solver.add(c)
        return [Value(f.functype.rets[0],r[0])],r[1],action
        # if type(r) == list:
        #     return [],state
    #当库函数没有被实现的时候就返回随机数了,目前改成了定值
    if f.funcname.startswith('db'):
        print("database op")
        print(f.funcname)
        print(valn)
    elif f.funcname == "send_inline":
        return [None],state,action
    if len(f.functype.rets) <= 0:
        if action == []:
            return [],state,action
        else:
            return [None],state,action
    if f.functype.rets[0] == bin_format.i32:
        r = randint(0,1)
        #0
    elif f.functype.rets[0] == bin_format.i64:
        r =randint(0,1)
        #0
    elif f.functype.rets[0] == bin_format.f32:
        r= uniform(0,1)
        #0.5
    else:
        r = uniform(0,1)
        #0.5
    return [Value(f.functype.rets[0], r)],state,action

# @profile
def wasmfunc_call(
        module: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack
):
    """The function call the internal wasm function.

    Args:
        module: the current module.
        address: the address of function.
        store: store the functions.
        stack: the current stack.

    Returns:
        r: the list of result, only one elem.
    """
    global primise,conclusion,action,gvar_cnt
    f: WasmFunc = store.funcs[address]
    has_father_function = len(global_vars.func_name_stack)>0
    last_func_name=global_vars.func_name_stack[-1] if has_father_function else 'not_func'
    global_vars.func_name_stack.append(str(address))
    if(len(global_vars.func_name_stack)>10):
        print("too long call depth:",str(address))
    next_func_name=global_vars.func_name_stack[-1]
    if next_func_name in global_vars.function_callcnt_map:
        global_vars.function_callcnt_map[next_func_name]=global_vars.function_callcnt_map[next_func_name]+1
    else:
        global_vars.function_callcnt_map[next_func_name]=0
    code = f.code.expr.data
    flag_not_print = 0
    flag_skip = 0
    func_name = list()
    if address - global_vars.library_offset > 32:
        print("address:"+str(address - global_vars.library_offset))
        if address-global_vars.library_offset  in library_function_dict.values():
            func_name = list(library_function_dict.keys())[list(library_function_dict.values()).index(address-global_vars.library_offset)]
        else:
            func_name=[next_func_name]
        global_vars.list_func.append(f'{func_name} {address} -> ')
        logger.infoln(f'wasmfunc call: {global_vars.list_func} ')

        if func_name == '$callvalue':
            if len(global_vars.list_func) > 2:
                global_vars.flag_getCallValue_in_function = True

    else:
        global_vars.list_func.append(f' {address} -> ')
        logger.infoln(f'wasmfunc call: {global_vars.list_func} ')
        pass
    if global_vars.skip_call:
        for _ in f.functype.args:
            stack.pop()
        # return [Value(f.functypes.rets[0],utils.gen_symbolic_value(f.functypes.rets[0],f"ret_val_{func_name}"))]

    valn = [stack.pop() for _ in f.functype.args][::-1]#盛放args
    
    # if has_father_function:
    #     call_args=[]
    #     for i in range(len(valn)):
    #         #primise.append(f"SubstVar{bin_format.valtype[(valn[i]).valtype][0][1:]}(complocalX{next_func_name}X{i},compstackX{last_func_name}X{stack.frame_len+i})")
    #         call_args.append(f"stackX{last_func_name}X{stack.frame_len+i}")
    #     call_args.extend(["globalX"+str(i) for i in range(len(store.globals))])
    val0 = []#盛放local(除去args)
    # if has_father_function:
    #     call_fact=gen_call_fact(last_func_name,next_func_name,"depth+'1'",*call_args)
    #     #conclusion.append(call_fact)
    #     local_vars=conclusion[0]
    #     # gvars=conclusion[1]
    #     #write_rule(primise,[],conclusion)
    # else:
    #     gvars=gen_gvars([],len(store.globals),gvar_cnt)

    #if func_name in emulator.realize_list_wasm:
        #r = emulator.wasmfunc_map['ethereum'][func_name](valn, solver, store)
        #if r:
            #flag_skip = 1
            #if len(r) == 4:
                #store.globals[module.globaladdrs[0]] = r[1]
                #store.globals[module.globaladdrs[1]] = r[2]
                #store.globals[module.globaladdrs[2]] = r[3]
                #r = [r[0]]

    for e in f.code.locals:
        if e == bin_format.i32:
            val0.append(Value.from_i32(0))
        elif e == bin_format.i64:
            val0.append(Value.from_i64(0))
        elif e == bin_format.f32:
            val0.append(Value.from_f32(0))
        else:
            val0.append(Value.from_f64(0))
    
    frame = Frame(module, valn + val0, len(f.functype.rets), len(code))

    if flag_skip != 1:
        stack.add(frame)
        stack.add(Label(len(f.functype.rets), len(code)))
        # An expression is evaluated relative to a current frame pointing to its containing module instance.
        # if has_father_function:
        #     # primise=[call_fact,gvars]
        #     primise=[call_fact.replace("depth+'1'","depth") if call_fact else call_fact]
        #     conclusion=[gen_tmr_vars(store, frame, stack.frame_len, module, next_func_name, 0)]
        #     #write_rule(primise,[],conclusion)
        # else:
        #     primise=[gvars]
        #     conclusion=[gen_tmr_vars(store, frame, stack.frame_len, module, next_func_name, 0,initial=True)]
        #     #write_rule(primise,[],conclusion)
        #     primise=[gvars,f"NEqVar(localX{next_func_name}X1,6138663591592764928)"]
        #     #write_rule(primise,["Fake_Constraint()"],conclusion)
        #     if global_vars.should_write_rule:
        #         gvar_cnt+=1
        r, new_stack, all_pc_traces = exec_expr(store, frame, stack, f.code.expr, -1)
        if global_vars.path_abort:
            # stack.data[:] = new_stack.data
            global_vars.func_name_stack.pop()
            global_vars.function_callcnt_map[next_func_name]=global_vars.function_callcnt_map[next_func_name]-1
            return r, all_pc_traces, []
        # if has_father_function:
        #     #conclusion.append(f"Return('{last_func_name}','{next_func_name}',depth,'{global_vars.function_callcnt_map[next_func_name]}',{','.join(['globalX'+str(i) for i in range(len(store.globals))])})")
        #     # #conclusion.append(gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt))
        #     if primise[0]:
        #         primise[0]=primise[0].replace("depth","depth+'1'")
        #     #write_rule(primise,action,conclusion)
        #     # primise=[f"Return('{next_func_name}')"]
        #     primise=[f"Return('{last_func_name}','{next_func_name}',depth,'{global_vars.function_callcnt_map[next_func_name]}',{','.join(['globalX'+str(i) for i in range(len(store.globals))])})"]
        #     #primise.append(local_vars)
        #     # #primise.append(gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt))
        #     # global_vars.gvar_cnt_stack.append(gvar_cnt)
        #     if global_vars.should_write_rule:
        #         gvar_cnt+=1
        # else:
        #     #这里是可以加End规则的地方
        #     pass

        # Exit
        print("exit func:",global_vars.list_func[-1])
        logger.infoln(f'{new_stack}')
        while not isinstance(new_stack.pop(), Frame):
            print(new_stack,next_func_name)
            if new_stack.len() <= 0:
                raise Exception('Signature mismatch in call!')
    else:
        # r需要仔细斟酌

        new_stack = copy.deepcopy(stack)
        
    tmp = global_vars.list_func.pop()

    logger.infoln(f'return func {tmp}')
    logger.infoln(f'{global_vars.list_func}')
    
    flag_skip = 0
    if flag_not_print == 1:
        flag_not_print = 0
        logger.lvl = global_vars.lvl

    stack.data[:] = new_stack.data
    global_vars.func_name_stack.pop()
    global_vars.function_callcnt_map[next_func_name]=global_vars.function_callcnt_map[next_func_name]-1
    return r, all_pc_traces, []


def fake_wasmfunc_call(
        module: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack
):
    """The fake function call the internal wasm function.


    Args:
        module: the current module.
        address: the address of function.
        store: store the functions.
        stack: the current stack.

    Returns:
        r: the list of fake result, only one elem at present.
    """
    # global func_cnt
    # func_cnt+=1
    # 这里最好还是返回符号值
    f: WasmFunc = store.funcs[address]
    valn = [stack.pop() for _ in f.functype.args][::-1]
    if len(f.functype.rets) <= 0:
        return []
    #return [Value(f.functype.rets[0], utils.gen_symbolic_value(f.functype.rets[0],f"return_val_{(func_cnt-1)}"))]
    if f.functype.rets[0] == bin_format.i32:
        r = randint(0, 1927)
        #r= utils.gen_symbolic_value(bin_format.i32,f"var")
       # r=100
    elif f.functype.rets[0] == bin_format.i64:
        r = randint(0, 1927)
        #r= utils.gen_symbolic_value(bin_format.i64,f"var")
        #r=100
    elif f.functype.rets[0] == bin_format.f32:
        r = uniform(0, 1)
        #r= utils.gen_symbolic_value(bin_format.f32,f"var")
        #r=0.5
    else:
        r = uniform(0, 1)
        #r= utils.gen_symbolic_value(bin_format.f64,f"var")
        #r=0.5
    return [Value(f.functype.rets[0], r)]


def call(
        module: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack,
        init_constraints: list = (),
):
    """The function call the internal wasm function or lib function.

    Args:
        module: the current module.
        address: the address of function.
        store: store the functions.
        stack: the current stack.
        init_constraints: initial function's args constraints.

    Returns:
        r: the list of result, only one elem.
    """
    f = store.funcs[address]
    assert len(f.functype.rets) <= 1
    for i, t in enumerate(f.functype.args[::-1]):
        ia = t
        ib = stack.data[-1 - i]
        if ia != ib.valtype:
            raise Exception('Signature mismatch in call!')

    init_variables(init_constraints)  # add initial constraints
    if isinstance(f, WasmFunc):
        return wasmfunc_call(module, address, store, stack)
    if isinstance(f, HostFunc):
        if f.funcname == "send_inline":
            global_vars.rollback=True
            print("rollback vulneralbility find")
        return hostfunc_call(module, address, store, stack)

# @profile
def fake_call(
        module: ModuleInstance,
        address: int,
        store: Store,
        stack: Stack,
        m=None
):
    """The function call the internal wasm function or lib function. 
    It does not execute lib function and only return a valid random 
    result.

    Args:
        module: the current module.
        address: the address of function.
        store: store the functions.
        stack: the current stack.

    Returns:
        r: the list of result, only one elem.
    """
    f = store.funcs[address]
    assert len(f.functype.rets) <= 1
    for i, t in enumerate(f.functype.args[::-1]):
        ia = t
        ib = stack.data[-1 - i]
        if isinstance(ib,Label) or ia != ib.valtype:
            raise Exception('Signature mismatch in call!')

    if isinstance(f, WasmFunc):
        # if global_vars.detection_mode:
        #     return fake_wasmfunc_call(module, address, store, stack)
        r = wasmfunc_call(module, address, store, stack)
        # print("call func$",str(address),r)
        return r
    if isinstance(f, HostFunc):
        if f.funcname == "send_inline":
            global_vars.rollback=True
            print("rollback vulneralbility find")
        return fake_hostfunc_call(module, address, store, stack, m)

# def set_stack_and_global()
    # [TODO] 


def spec_br(l: int, stack: Stack) -> int:
    """Process branch instruction.

    Args:
        l: the pc of Label.
        stack: the runtime stack.
    
    Returns:
        result: the target position of branch instruction.
    """
    # Let L be hte l-th label appearing on the stack, starting from the top and counting from zero.
    L = [i for i in stack.data if isinstance(i, Label)][::-1][l]
    n = L.arity
    v = [stack.pop() for _ in range(n)][::-1]

    s = 0
    while True:
        e = stack.pop()
        if isinstance(e, Label):
            s += 1
            if s == l + 1:
                break
    stack.ext(v)
    return L.continuation - 1


def init_variables(init_constraints: list = ()) -> None:
    """Initialize the variables.
    """
    global path_condition, memory_address_symbolic_variable, gas_cost, solver, \
        recur_depth, loop_depth_dict,  path_depth, block_number_flag
    solver = z3.Solver()
    solver.add(init_constraints)
    path_condition = list(init_constraints)
    memory_address_symbolic_variable = {}
    recur_depth = 0
    loop_depth_dict = defaultdict(int)
    global_vars.path_abort = False
    path_depth = 0
    block_number_flag = False
    gas_cost = 0

def is_visited(visited,addr):
    for i,p in enumerate(visited):
        if(p[0]<=addr and p[1]>=addr):
            return True
    return False

def gen_tmr_vars(store, frame, stack_frame_len, module, func_name, pc, initial=False,has_global=False):
    global rule_cnt
    if not global_vars.should_write_rule:
        return
    callcnt=global_vars.function_callcnt_map[func_name]
    if not has_global:
        res="Var_"+bin(pc)[2:]+"("
    else:
        res="Var_"+bin(pc)[2:]+"_local("
    if initial:
        tmr_vars=[f"'{func_name}'","'0'",f"'{callcnt}'"]
    else:
        tmr_vars=[f"'{func_name}'","depth",f"'{callcnt}'"]
    if not has_global:
        # tmr_vars.extend(["memoryX"+str(i) for i in range(len(store.mems[module.memaddrs[0]].data))])
        # tmr_vars.append("memory")
        tmr_vars.extend(["globalX"+str(i) for i in range(len(store.globals))])
    tmr_vars.extend(["localX"+func_name+'X'+str(i) for i in range(len(frame.locals))])
    for i in range(stack_frame_len):
        tmr_vars.append("stackX"+func_name+'X'+str(i))
    res+=','.join(tmr_vars)
    res+=")"
    return res

def gen_gvars(data,globals_len, gcnt):
    if not global_vars.should_write_rule:
        return
    res="GVar_"+bin(gcnt)[2:]+"("
    gvars=[]
    # gvars.extend(["memoryX"+str(i) for i in range(len(data))])
    # gvars.append("memory")
    gvars.extend(["globalX"+str(i) for i in range(globals_len)])
    res+=','.join(gvars)
    res+=")"
    return res

def gen_call_fact(func_name:str,next_func_name,*vars):
    global rule_cnt
    if not global_vars.should_write_rule:
        return
    global call_cnt
    res="Call"+func_name+"_"+str(call_cnt)+"('"+next_func_name+"',"
    res+=",".join(vars)
    res+=")"
    return res


def write_rule(primise,action,conclusion,primise_choices=None,conclusion_choices=None):
    #TODO: 测试完成后可以加上去重的部分
    global rule_cnt
    if not global_vars.should_write_rule:
        return
    if not primise_choices:
        global_vars.output_a_line(f"rule Rule_{bin(rule_cnt)[2:]}:")
        global_vars.output_a_line(f"[{','.join(primise)}]--[{','.join(action)}]->[{','.join(conclusion)}]")
        global_vars.output_a_line("")
        rule_cnt+=1
    else:
        for i,pc in enumerate(primise_choices):
            #primise.extend(pc)
            #if(conclusion_choices and conclusion_choices[i]):
                #conclusion.append(conclusion_choices[i])
            global_vars.output_a_line(f"rule Rule_{bin(rule_cnt)[2:]}:")
            global_vars.output_a_line(f"[{','.join(primise)}]--[{','.join(action)}]->[{','.join(conclusion)}]")
            global_vars.output_a_line("")
            rule_cnt+=1
            primise.pop()
            if(conclusion_choices and conclusion_choices[i]):
                conclusion.pop()


def print_red(s:str):
    print("\033[31;5m"+s+"\033[0m")

def transfer_signature_check(f):
    transfer_signature=[bin_format.i64,bin_format.i64,bin_format.i32,bin_format.i32]
    if len(f.functype.args)<4:
        return False
    elif len(f.functype.args)>4:
        a=f.functype.args[-4:]
    else:
        a=f.functype.args
    for i, t in enumerate(a):
        ia = t
        ib = transfer_signature[i]
        if ib != ia:
            return False 
    return True

def is_blockchain_state(var):
    blockchain_state_operation=["current_time","tapos_block_prefix","tapos_block_num"]
    for c in blockchain_state_operation:
        # print("blockvar")
        # print(var)
        try:
            if c in var.name:
                return True
        except:
            return True

    return False

# @profile
def exec_expr(
        store: Store,
        frame: Frame,
        stack: Stack,
        expr: structure.Expression,
        pc: int = -1,
):
    """An expression is evaluated relative to a current frame pointing to its containing module instance.
    1. Jump to the start of the instruction sequence instr∗ of the expression.
    2. Execute the instruction sequence.
    3. Assert: due to validation, the top of the stack contains a value.
    4. Pop the value val from the stack.

    Args:
        store: the function address of current module
        frame: current runtime frame
        stack: the stack for current state
        expr: the instructions to execute
        pc: the program counter

    Returns:
        stack and executed result

    Raises:
        AttributeError: if the Label instance is read for getting value
        z3Exception: if the symbolic variable is converted
    """
    global  path_depth, recur_depth, loop_depth_dict, block_number_flag, gas_cost, path_condition, primise, conclusion, call_cnt,  gvar_cnt
    branch_res = []
    pc_state = [GlobalState()]
    all_pc_states = []
    module = frame.module
    func_name=global_vars.func_name_stack[-1] if len(global_vars.func_name_stack)>0 else 'not_func'
    if not expr.data:
        raise Exception('Empty init expr!')

    while True:
        global_vars.cur_sum_pc += 1
        pc += 1#这个pc是函数内偏移
        for i,v in enumerate(pc_state):
            pc_state[i].add_pc((0 if func_name=='not_func' else int(func_name),pc))
        # print(pc_state)
        primise=[]
        action=[]
        oaction=[]
        oprimise=[]
        conclusion=[]
        primise_choices=[]
        conclusion_choices=[]
        #primise.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc))
        if not global_vars.cut_on_unsat and (func_name,pc) in global_vars.pc_cnts:
            global_vars.path_abort=True
        global_vars.pc_cnts.add((func_name,pc))

        if global_vars.path_abort or pc >= len(expr.data):
            all_pc_states.extend(pc_state[:])
            print("break of path_abort or out of scope",global_vars.path_abort)
            break

        # Analysis current state to update some variables and detect vulneralbility
        # if global_vars.detection_mode:
        #     cur_state_analysis(store, frame, stack, expr, pc, solver)#这里进行了漏洞逻辑的判断,以及对于N函数的结果构造和跳转
        #     pc = global_vars.pc

        i = expr.data[pc]

        logger.infoln(f'{str(i) :<18} {stack} {pc} {global_vars.cur_sum_pc} {func_name}')
        # m = store.mems[module.memaddrs[0]]
        # if number.MemoryLoad.i32(m.data[4:8])>0x6300:
        #     print("too large")
        #这里是为了找出rollback合约为什么内存越界

        # accumulate the gas cost to detect expensive fallback
        gas_cost += bin_format.gas_cost.get(i, 0)
        global_vars.max_gas_cost = max(global_vars.max_gas_cost, gas_cost)

        if logger.lvl >= 2:
            ls = [f'{i}: {bin_format.valtype[l.valtype][0]} {l.n}' for i, l in enumerate(frame.locals)]
            gs = [f'{i}: {"mut " if g.mut else ""}{bin_format.valtype[g.value.valtype][0]} {g.value.n}' for i, g in
                  enumerate(store.globals)]
            for n, e in (('locals', ls), ('globals', gs)):
                logger.verboseln(f'{" " * 18} {str(n) + ":":<8} [{", ".join(e)}]')

        opcode = i.code
        if bin_format.unreachable <= opcode <= bin_format.call_indirect:
            if opcode == bin_format.unreachable:
                global_vars.unreachable_count += 1
                # raise Exception('unreachable')
                break
            if opcode == bin_format.nop:
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.block:
                arity = int(i.immediate_arguments != bin_format.empty)
                stack.add(Label(arity, expr.composition[pc][-1] + 1))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.loop:
                stack.add(Label(0, expr.composition[pc][0]))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.if_:
                object_c = stack.pop()
                c = object_c.n
                arity = int(i.immediate_arguments != bin_format.empty)
                stack.add(Label(arity, expr.composition[pc][-1] + 1))
                if utils.is_all_real(c):
                    if c != 0:
                        #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                        #write_rule(primise,action,conclusion)
                        continue
                    if len(expr.composition[pc]) > 2:
                        pc = expr.composition[pc][1]
                        #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                        #write_rule(primise,action,conclusion)
                        continue
                    pc = expr.composition[pc][-1] - 1
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                else:
                    len_solver_scope=solver.num_scopes()
                    solver.push()
                    solver.add(c != 0)
                    find_symbolic_in_solver(solver)
                    check_mishandled_exception(solver, global_vars.cur_sum_pc)
                    logger.debugln(solver)
                    logger.infoln(f'left branch ({func_name} {pc}: {i})')
                    old_path_depth=path_depth 
                    path_depth += 1
                    len_list_func = len(global_vars.list_func)
                    len_path_condition = len(path_condition)
                    global_vars.len_list_func = len(global_vars.list_func)
                    if recur_depth > global_vars.BRANCH_DEPTH_LIMIT:
                        all_pc_states.extend(pc_state[:])
                        global_vars.path_abort=True
                        if utils.is_symbolic(c): #and c
                            logger.infoln(f'recur {recur_depth}')
                            solver.pop()
                            # raise Exception('recur')
                            # 有时候返回数字0回栈顶不是个好的选择，如果if判断的栈顶元素是位向量，且内容为0，那么我们就返回它本身

                            return [object_c], global_vars.last_stack[-1], all_pc_states
                        return [], global_vars.last_stack[-1], all_pc_states
                    global_vars.last_stack.append(stack)
                    try:
                        if global_vars.cut_on_unsat and solver.check() == z3.unsat:
                            logger.infoln(f'({pc}: {i}) infeasible path detected!')
                            left_new_stack = None
                        else:
                            # Execute the left branch
                            # new_store = copy.deepcopy(store)
                            new_frame = copy.deepcopy(frame)
                            left_new_stack = copy.deepcopy(stack)
                            new_store = store
                            # new_frame = frame
                            # left_new_stack = stack
                            new_expr = expr
                            new_pc = pc
                            block_number_flag = id(c) in global_vars.block_number_id_list or block_number_flag  # set flag if "c" is associated with the block number
                            old_call_authenticate=global_vars.call_authenticate
                            old_call_block_state=global_vars.call_block_state
                            path_condition.append(c != 0)
                            for p in pc_state:
                                p.add_constraint(c!=0)
                            recur_depth += 1
                            gas_cost -= bin_format.gas_cost.get(i, 0)
                            global_vars.sum_pc.append(global_vars.cur_sum_pc)
                            #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},1)")
                            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                            #write_rule(primise,action,conclusion)
                            # primise.pop()
                            # conclusion.pop()
                            left_branch_res, left_new_stack, left_pc_traces = exec_expr(new_store, new_frame, left_new_stack, new_expr, new_pc)

                            logger.infoln(f'leave left branch {func_name} {pc}')
                            global_vars.call_authenticate=old_call_authenticate
                            global_vars.call_block_state=old_call_block_state
                            gas_cost += bin_format.gas_cost.get(i, 0)
                            recur_depth -= 1
                            if global_vars.cut_on_unsat:
                                all_pc_states += [i+p for i in pc_state for p in left_pc_traces if not p.is_empty()]
                                print("size of all_pc_states",sys.getsizeof(all_pc_states))
                            if global_vars.path_abort:
                                global_vars.path_abort = False
                                left_new_stack = None
                            else:
                                branch_res += left_branch_res
                                if len(left_branch_res) <= 1:
                                    global_vars.add_cond_and_results(path_condition[:], left_branch_res[:])
                            path_condition = path_condition[:len_path_condition]
                            for p in pc_state:
                                p.delete_constraint()
                    except TimeoutError:
                        logger.infoln('Timeout in path exploration.')
                    except Exception as e:
                        logger.infoln(f'Exception: {e}')
                        global_vars.cur_sum_pc = global_vars.sum_pc.pop()
                        global_vars.list_func = global_vars.list_func[:len_list_func]
                        path_condition = path_condition[:len_path_condition]
                        for p in pc_state:
                            p.delete_constraint()
                        recur_depth -= 1

                    m = store.mems[module.memaddrs[0]]
                    list_solver = solver.units()
                    vars = get_vars(list_solver[-1])
                    for var in vars:
                        if str(var) == 'callDataCopy_0':
                            if len(global_vars.list_func) == 1:
                                global_vars.clear_dict_symbolic_address()


                    path_depth =old_path_depth

                    while solver.num_scopes()!=len_solver_scope:
                        solver.pop()
                    solver.push()
                    solver.add(c == 0)
                    find_symbolic_in_solver(solver)
                    logger.debugln(solver)
                    logger.infoln(f'right branch ({func_name} {pc}: {i})')
                    try:
                        if global_vars.cut_on_unsat and solver.check() == z3.unsat:
                            logger.infoln(f'({pc}: {i}) infeasible path detected!')
                            right_new_stack=None
                        else:
                            # Execute the right branch
                            # new_store = copy.deepcopy(store)
                            new_frame = copy.deepcopy(frame)
                            right_new_stack = copy.deepcopy(stack)
                            new_store = store
                            # new_frame = frame
                            # right_new_stack=stack
                            new_expr = copy.deepcopy(expr)
                            new_pc = expr.composition[pc][1] if len(expr.composition[pc]) > 2 else expr.composition[pc][-1] - 1
                            #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},0)")
                            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, new_pc+1))
                            #write_rule(primise,action,conclusion)
                            block_number_flag = True if id(
                                c) in global_vars.block_number_id_list else block_number_flag  # set flag if "c" is associated with the block number
                            old_call_authenticate=global_vars.call_authenticate
                            old_call_block_state=global_vars.call_block_state
                            path_condition.append(c == 0)
                            for p in pc_state:
                                p.add_constraint(c==0)
                            recur_depth += 1
                            gas_cost -= bin_format.gas_cost.get(i, 0)
                            global_vars.sum_pc.append(global_vars.cur_sum_pc)
                            right_branch_res, right_new_stack, right_pc_traces = exec_expr(new_store, new_frame, right_new_stack, new_expr, new_pc)
                            logger.infoln(f'leave right branch {func_name} {pc}')
                            global_vars.call_authenticate=old_call_authenticate
                            global_vars.call_block_state=old_call_block_state
                            logger.debugln(right_new_stack)
                            gas_cost += bin_format.gas_cost.get(i, 0)
                            recur_depth -= 1
                            if global_vars.cut_on_unsat:
                                all_pc_states += [i+p for i in pc_state for p in right_pc_traces if not p.is_empty()]
                                print("size of all_pc_states",sys.getsizeof(all_pc_states))
                            if global_vars.path_abort:
                                global_vars.path_abort=False
                                # if path_depth <= 0:
                                #     temp_stack = Stack()
                                #     temp_stack.add(frame)
                                #     return branch_res, temp_stack, all_pc_states
                                # else:
                                right_new_stack = None
                            else:
                                branch_res += right_branch_res
                                if len(right_branch_res) <= 1:
                                    global_vars.add_cond_and_results(path_condition[:], right_branch_res[:])
                            path_condition = path_condition[:len_path_condition]
                            for p in pc_state:
                                p.delete_constraint()
                    except TimeoutError as e:
                        raise e
                    except Exception as e:
                        logger.infoln(f'Exception: {e}')
                        global_vars.cur_sum_pc = global_vars.sum_pc.pop()
                        global_vars.list_func = global_vars.list_func[:len_list_func]
                        path_condition = path_condition[:len_path_condition]
                        for p in pc_state:
                            p.delete_constraint()
                        traceback.print_exc()
                        print('line:', e.__traceback__.tb_lineno)
                        recur_depth -= 1

                    while solver.num_scopes()!=len_solver_scope:
                        solver.pop()
                    # if path_depth <= 0:
                    #     temp_stack = Stack()
                    #     temp_stack.add(frame)
                    #     return branch_res, temp_stack, all_pc_states
                    global_vars.last_stack.pop()
                    if left_new_stack is None and right_new_stack is None:
                        left_new_stack=copy.deepcopy(stack)
                        global_vars.path_abort=True
                    return branch_res, left_new_stack if left_new_stack is not None else right_new_stack, all_pc_states

            if opcode == bin_format.else_:
                for i in range(len(stack.data)):
                    i = -1 - i
                    e = stack.data[i]
                    if isinstance(e, Label):
                        pc = e.continuation - 1
                        logger.debugln(pc)
                        del stack.data[i]
                        break
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.end:
                # label{instr*} val* end -> val*
                if stack.status() == Label:
                    for i in range(len(stack.data)):
                        i = -1 - i#反向遍历
                        if isinstance(stack.data[i], Label):
                            del stack.data[i]
                            break
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                # frame{F} val* end -> val*
                v = [stack.pop() for _ in range(frame.arity)][::-1]
                stack.ext(v)
                # if len(global_vars.func_name_stack)>0:
                    # #conclusion.append(f"Return({func_name})")
                    # last_gvar_cnt=global_vars.gvar_cnt_stack.pop()
                    # gvars=gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt)
                    # #conclusion.append(gvars)
                    # #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.br:
                # too many loop depth
                if loop_depth_dict[i.immediate_arguments] > global_vars.LOOP_DEPTH_LIMIT:
                    print(loop_depth_dict)
                    global_vars.path_abort=True
                    # loop_depth_dict[i.immediate_arguments]=0
                    all_pc_states.extend(pc_state[:])
                    print("meet LOOP DEPTH LIMIT")
                    break
                # record the loop depth
                loop_depth_dict[i.immediate_arguments] += 1
                pc = spec_br(i.immediate_arguments, stack)
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.br_if:
                c = stack.pop().n
                if global_vars.cut_on_unsat and utils.is_all_real(c):
                    # too many loop depth
                    if loop_depth_dict[i.immediate_arguments] > global_vars.LOOP_DEPTH_LIMIT:
                        print(loop_depth_dict)
                        # loop_depth_dict[i.immediate_arguments]=0
                        global_vars.path_abort=True
                        print("meet LOOP DEPTH LIMIT")
                        all_pc_states.extend(pc_state[:])
                        break
                    if c == 0:
                        print("not jump")
                        #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},0)")
                        #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                        #write_rule(primise,action,conclusion)
                        continue

                    # record the loop depth
                    print("should jump")
                    loop_depth_dict[i.immediate_arguments] += 1
                    pc = spec_br(i.immediate_arguments, stack)
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},1)")
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                else:
                    len_solver_scope=solver.num_scopes()
                    old_loop_depth_dict=copy.deepcopy(loop_depth_dict)
                    solver.push()
                    solver.add(c == 0)
                    find_symbolic_in_solver(solver)
                    logger.infoln(f'left branch ({func_name} {pc}: {i})')
                    old_path_depth = path_depth
                    path_depth += 1
                    print("path depth",path_depth)
                    if recur_depth > global_vars.BRANCH_DEPTH_LIMIT:
                        print("meet BRANCH DEPTH LIMIT")
                        all_pc_states.extend(pc_state[:])
                        global_vars.path_abort=True
                        return branch_res, global_vars.last_stack[-1] if global_vars.last_stack != [] else None, all_pc_states
                    global_vars.last_stack.append(stack)
                    try:
                        if global_vars.cut_on_unsat and solver.check() == z3.unsat:
                            logger.infoln(f'({pc}: {i}) infeasible path detected!')
                            left_new_stack = None
                        else:
                            # Execute the left branch
                            # new_store = copy.deepcopy(store)
                            new_frame = copy.deepcopy(frame)
                            new_store = store
                            # new_frame = frame
                            left_new_stack = copy.deepcopy(stack)
                            new_expr = expr
                            new_pc = pc
                            block_number_flag = id(
                                c) in global_vars.block_number_id_list or block_number_flag  # set flag if "c" is associated with the block number
                            old_call_authenticate=global_vars.call_authenticate
                            old_call_block_state=global_vars.call_block_state
                            path_condition.append(c == 0)
                            for p in pc_state:
                                p.add_constraint(c==0)
                            recur_depth += 1
                            gas_cost -= bin_format.gas_cost.get(i, 0)
                            #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},1)")
                            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, new_pc+1))
                            #write_rule(primise,action,conclusion)
                            # primise.pop()
                            # conclusion.pop()
                            left_branch_res, left_new_stack, left_pc_traces = exec_expr(new_store, new_frame, left_new_stack, new_expr, new_pc)
                            gas_cost += bin_format.gas_cost.get(i, 0)
                            recur_depth -= 1
                            if global_vars.cut_on_unsat:
                                all_pc_states += [i+p for i in pc_state for p in left_pc_traces if not p.is_empty()]
                                print("size of all_pc_states",sys.getsizeof(all_pc_states))
                            if global_vars.path_abort:
                                global_vars.path_abort = False
                                left_new_stack = None
                            else:
                                branch_res += left_branch_res
                                if len(left_branch_res) == 1:
                                    global_vars.add_cond_and_results(path_condition[:], left_branch_res[:])
                            global_vars.call_authenticate=old_call_authenticate
                            global_vars.call_block_state=old_call_block_state
                            path_condition.pop()
                            for p in pc_state:
                                p.delete_constraint()
                    except TimeoutError:
                        raise
                    except Exception as e:
                        logger.infoln(f'Exception {e}')
                        traceback.print_exc()
                    path_depth = old_path_depth+1
                    print("len_solver_scope:",len_solver_scope)
                    while solver.num_scopes()!=len_solver_scope:
                        solver.pop()
                    print("after pop:",solver.num_scopes())

                    solver.push()
                    solver.add(c != 0)
                    find_symbolic_in_solver(solver)
                    logger.infoln(f'right branch ({func_name} {pc}: {i})')
                    try:
                        # print(solver)
                        if global_vars.cut_on_unsat and solver.check() == z3.unsat:
                            logger.infoln(f'({pc}: {i}) infeasible path detected!')
                            right_new_stack=None
                        else:
                            # Execute the right branch
                            # new_store = copy.deepcopy(store)
                            new_frame = copy.deepcopy(frame)
                            new_store = store
                            # new_frame = frame
                            right_new_stack = copy.deepcopy(stack)
                            new_expr = expr
                            new_pc = spec_br(i.immediate_arguments, right_new_stack)
                            block_number_flag = True if id(
                                c) in global_vars.block_number_id_list else block_number_flag  # set flag if "c" is associated with the block number
                            old_call_authenticate=global_vars.call_authenticate
                            old_call_block_state=global_vars.call_block_state
                            loop_depth_dict=old_loop_depth_dict
                            path_condition.append(c != 0)
                            for p in pc_state:
                                p.add_constraint(c!=0)
                            recur_depth += 1
                            gas_cost -= bin_format.gas_cost.get(i, 0)
                            #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},0)")
                            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, new_pc+1))
                            #write_rule(primise,action,conclusion)
                            right_branch_res, right_new_stack, right_pc_traces = exec_expr(new_store, new_frame, right_new_stack, new_expr, new_pc)
                            gas_cost += bin_format.gas_cost.get(i, 0)
                            recur_depth -= 1
                            if global_vars.cut_on_unsat:
                                print("size of all_pc_states",sys.getsizeof(all_pc_states))
                                all_pc_states += [i+p for i in pc_state for p in right_pc_traces if not p.is_empty()]
                            if global_vars.path_abort:
                                global_vars.path_abort=False
                                print("path abort")
                                # if path_depth <= 0:
                                #     print("path abort<=0")
                                #     temp_stack = Stack()
                                #     temp_stack.add(frame)
                                #     return branch_res, temp_stack, all_pc_states
                                # else:
                                right_new_stack = None
                            else:
                                branch_res += right_branch_res
                                if len(right_branch_res) <= 1:
                                    global_vars.add_cond_and_results(path_condition[:], right_branch_res[:])
                            global_vars.call_authenticate=old_call_authenticate
                            global_vars.call_block_state=old_call_block_state
                            path_condition.pop()
                            for p in pc_state:
                                p.delete_constraint()
                    except TimeoutError:
                        raise
                    except Exception as e:
                        logger.infoln(f'Exception {e}')
                        traceback.print_exc()

                    while solver.num_scopes()!=len_solver_scope:
                        solver.pop()
                    # if path_depth <= 0:
                    #     print("path depth<=0",path_depth)
                    #     temp_stack = Stack()
                    #     temp_stack.add(frame)
                    #     return branch_res, temp_stack, all_pc_states
                    global_vars.last_stack.pop()
                    if left_new_stack is None and right_new_stack is None:
                        leftnew_stack=copy.deepcopy(stack)
                        global_vars.path_abort=True
                    return branch_res, left_new_stack if left_new_stack is not None else right_new_stack, all_pc_states

            # TODO:symbolic execution
            if opcode == bin_format.br_table:
                a = i.immediate_arguments[0]
                l = i.immediate_arguments[1]
                c = stack.pop().n
                if 0 <= c < len(a):
                    l = a[c]
                pc = spec_br(l, stack)
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue

            if opcode == bin_format.return_:
                v = [stack.pop() for _ in range(frame.arity)][::-1]
                # #conclusion.append(f"Return('{func_name}')")
                # last_gvar_cnt=global_vars.gvar_cnt_stack.pop()
                # gvars=gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt)
                # #conclusion.append(gvars)
                #write_rule(primise,action,conclusion)

                while True:
                    e = stack.pop()
                    if isinstance(e, Frame):
                        stack.add(e)
                        break
                stack.ext(v)
                all_pc_states.extend(pc_state[:])
                break
            

            if opcode == bin_format.call:
                #TODO: 需要区分一下特殊的函数调用，比如transfer之类的
                m = store.mems[module.memaddrs[0]]
                # global_vars.skip_call=True
                if global_vars.location_mode and transfer_signature_check(store.funcs[module.funcaddrs[i.immediate_arguments]]): #     #如果是通过call调用但是签名匹配也看作是找到了transfer函数
                    # found transfer index!
                    global_vars.transfer_function_address=i.immediate_arguments
                    # global_vars.transfer_function_params=utils.gen_transfer_symbolic_args(store.funcs[module.funcaddrs[i.immediate_arguments]])
                    global_vars.transfer_function_params=utils.gen_symbolic_args(store.funcs[module.funcaddrs[i.immediate_arguments]])
                    global_vars.function_name_stack=[]
                    raise SystemExit('found transfer function')
                call_cnt=pc
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc, has_global=True))
                # #conclusion.append(gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt))
                if global_vars.should_write_rule:
                    gvar_cnt+=1
                #next_vars=gen_tmr_vars(store, frame, stack.frame_len-len(store.funcs[module.funcaddrs[i.immediate_arguments]].functype.args), module, func_name, pc+1)
                old_stack=copy.deepcopy(stack)
                r,call_pc_traces,action= fake_call(module, module.funcaddrs[i.immediate_arguments], store, stack, m)
                temp_pc_trace=[]
                for p in pc_state:
                    for t in call_pc_traces:
                        temp_pc_trace.append(p+t)
                # print("global_vars.cut_on_unsat",global_vars.cut_on_unsat)
                if global_vars.cut_on_unsat:
                    pc_state=temp_pc_trace
                    # print("cons")
                    # print([i.constraints for i in pc_state])
                if global_vars.path_abort:
                    stack=old_stack
                    continue
                print("size of pc_state",sys.getsizeof(pc_state))
                # if len(r)>1:
                    # action=r[1]
                    # r=r[:1]
                print("action:",action)
                #conclusion=[next_vars]
                #write_rule(primise,action,conclusion)
                # global_vars.skip_call=False
                if len(r)>0 and r[0]!=None:
                    stack.ext(r)

                if global_vars.flag_revert > 0:
                    global_vars.clear_flag_revert()
                    raise Exception('call eth.revert')

                # store the address of the block number or block prefix
                if module.funcaddrs[i.immediate_arguments] in global_vars.tapos_block_function_addr:
                    global_vars.add_random_number_id(id(r[0]))

                # detect the send token call
                if module.funcaddrs[i.immediate_arguments] in global_vars.send_token_function_addr:
                    check_block_dependence_old(block_number_flag)

                # detect the ethereum delegate call
                if module.funcaddrs[i.immediate_arguments] in global_vars.call_delegate_addr:
                    check_ethereum_delegate_call(expr.data[pc - 1])
                


                # detect the ethereum greedy bug: is the function called a payable?
                check_ethereum_greedy(module.funcaddrs[i.immediate_arguments])

                continue

            if opcode == bin_format.call_indirect:
                m = store.mems[module.memaddrs[0]]
                if i.immediate_arguments[1] != 0x00:
                    raise Exception('Zero byte malformed in call_indirect!')
                call_type=module.types[i.immediate_arguments[0]]
                print("call_type: ", call_type)
                idx = stack.pop().n
                tab = store.tables[module.tableaddrs[0]]
                def check_args(idx):
                    if call_type==():
                        return True
                    f=store.funcs[tab.elem[idx]]
                    return f.functype==call_type
                    
                    #for i, t in enumerate(f.functype.args[::-1]):
                        #ia = t
                        #ib = stack.data[-1 - i]
                        #if isinstance(ib,Label) or ia != ib.valtype:
                           #return False 
                    #return True
                loop_cnt=0
                test_idx=idx
                while utils.is_symbolic(idx) or idx not in range(len(tab.elem)) or tab.elem[idx] is None or not check_args(idx):
                    #如果这里传入的call_indirect的表项不存在就循环，但是这样一个是循环可能不会停止，一个是没有进行参数的校验，但是fake_call里却进行了校验
                    #这样的问题源于，因为loop_depth和branch_depth的限制，可能会提前停止
                    if loop_cnt>10:
                        break
                    logger.println('Invalid function index in table.')
                    test_idx = randint(0, len(tab.elem) - 1)
                    #改成idx=2是为了测试rollback的确定分支
                    #TODO: 这里可以改成多分支的情况
                    # idx=2
                    print("test idx:",test_idx)
                    print("tab:",tab.elem[test_idx])
                    loop_cnt+=1
                if loop_cnt>10:
                    print("no useable table idx")
                    all_pc_states.extend(pc_state[:])
                    break
                print("use random table idx",test_idx)
                if utils.is_symbolic(idx):
                    path_condition.append(idx==test_idx)
                    for p in pc_state:
                        p.add_constraint(idx==test_idx)

                if global_vars.location_mode:
                    # found transfer index!
                    global_vars.transfer_function_index = idx
                    global_vars.transfer_function_params=utils.gen_symbolic_args(store.funcs[tab.elem[idx]])
                    global_vars.function_name_stack=[]
                    raise SystemExit('found transfer function')
                call_cnt=pc
                #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len},{idx})")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc, has_global=True))
                # #conclusion.append(gen_gvars(store.mems[module.memaddrs[0]].data,len(store.globals),gvar_cnt))
                if global_vars.should_write_rule:
                    gvar_cnt+=1
                #next_vars=gen_tmr_vars(store, frame, stack.frame_len-len(store.funcs[tab.elem[idx]].functype.args), module, func_name, pc+1)
                r,call_pc_traces,action = fake_call(module, tab.elem[idx], store, stack,m)
                temp_pc_trace=[]
                for i in pc_state:
                    for t in call_pc_traces:
                        temp_pc_trace.append(i+t)
                if global_vars.cut_on_unsat:
                    pc_state=temp_pc_trace
                print("size of pc_state",sys.getsizeof(pc_state))
                # if len(r)>1:
                    # action=r[1]
                    # r=r[:1]
                #write_rule(primise,action,[next_vars])
                stack.ext(r)

                # there may exists random number bug, therefore count the function call
                if tab.elem[idx] in global_vars.tapos_block_function_addr:
                    global_vars.add_random_number_id(id(r[0]))


                # detect the ethereum greedy bug: is the function called a payable?
                # check_ethereum_greedy(module.funcaddrs[i.immediate_arguments])
                continue
            continue

        if opcode == bin_format.drop:
            stack.pop()
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if opcode == bin_format.select:
            cond = stack.pop().n
            a = stack.pop()
            b = stack.pop()
            if utils.is_all_real(cond):
                if cond:
                    # if b.valtype in (bin_format.i32, bin_format.f32):
                    #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len})")
                    # else:
                    #     #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len})")
                    stack.add(b)
                else:
                    # if a.valtype in (bin_format.i32, bin_format.f32):
                    #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})")
                    # else:
                    #     #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})")
                    stack.add(a)
            else:
                a.n = (utils.to_symbolic(a.n, 32) if a.valtype in (bin_format.i32, bin_format.f32)
                       else utils.to_symbolic(a.n, 64))
                b.n = (utils.to_symbolic(b.n, 32) if a.valtype in (bin_format.i32, bin_format.f32)
                       else utils.to_symbolic(b.n, 64))
                computed = Value(a.valtype, z3.simplify(z3.If(cond == 0, a.n, b.n)))
                # if b.valtype in (bin_format.i32, bin_format.f32):
                #     #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len+2},1)"\
                #             ,f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len})"])
                # else:
                #     #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len+2},1)"\
                #             ,f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len})"])
                # if a.valtype in (bin_format.i32, bin_format.f32):
                #     #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len+2},1)"\
                #             ,f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"])
                # else:
                #     #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len+2},1)"\
                #             ,f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"])
                stack.add(computed)
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion,primise_choices)
            continue

        if opcode == bin_format.get_local:
            e=frame.locals[i.immediate_arguments]
            # if e.valtype in (bin_format.i32, bin_format.f32):
            #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},complocalX{func_name}X{i.immediate_arguments})")
            # else:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},complocalX{func_name}X{i.immediate_arguments})")
                #TODO: SubstVar64需要根据名字只添加64位的BV,还有32位的和8位的
            stack.add(e)
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if opcode == bin_format.set_local:
            if i.immediate_arguments >= len(frame.locals):
                #print("越界")
                frame.locals.extend([Value.from_i32(0) for _ in range(i.immediate_arguments - len(frame.locals) + 1)])
            #primise.append(f"SubstVar(complocalX{func_name}X{i.immediate_arguments},compstackX{func_name}X{stack.frame_len})")
            tmp = stack.pop()
            frame.locals[i.immediate_arguments] = tmp
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if opcode == bin_format.tee_local:
            #primise.append(f"SubstVar(complocalX{func_name}X{i.immediate_arguments},compstackX{func_name}X{stack.frame_len})")
            frame.locals[i.immediate_arguments] = stack.top()
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if opcode == bin_format.get_global:
            # [TODO]
            if len(store.globals) <= 0:
                stack.add(Value.from_i32(0))
            else:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compglobalX{i.immediate_arguments})")
                stack.add(store.globals[module.globaladdrs[i.immediate_arguments]].value)
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
            continue

        if opcode == bin_format.set_global:
            #primise.append(f"SubstVar(compglobalX{func_name}X{i.immediate_arguments},compstackX{func_name}X{stack.frame_len})")
            store.globals[module.globaladdrs[i.immediate_arguments]] = GlobalInstance(stack.pop(), True)
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if bin_format.i32_load <= opcode <= bin_format.grow_memory:
            m = store.mems[module.memaddrs[0]]
            if bin_format.i32_load <= opcode <= bin_format.i64_load32_u:
                logger.verboseln(f'm.data state {m.data}')
                # logger.debugln(f'm.data state {m.data}')
                a = stack.pop().n + i.immediate_arguments[1]
                if utils.is_symbolic(a):
                    m=store.smems[module.memaddrs[0]]
                    print(f"{pc}:{i.__repr__()} {a.__repr__()}\n")
                    # global_vars.output.write(f"{pc}:{i.__repr__()} {a.__repr__()}\n")
                    a = z3.simplify(a)
                    if opcode == bin_format.i32_load:
                        # stack.add(Value.from_i32(utils.gen_symbolic_value(bin_format.i32,f"i32_bv_mem_{pc}")))
                        stack.add(Value.from_i32(number.MemoryLoad.i32(
                            m.load(a,4))))
                        continue
                    if opcode == bin_format.i64_load:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.i64(
                            m.load(a,8))))
                        continue
                    if opcode == bin_format.f32_load:
                        # stack.add(Value.from_f32(utils.gen_symbolic_value(bin_format.f32,str(pc))))
                        stack.add(Value.from_f32(number.MemoryLoad.f32(
                            m.load(a,4))))
                        continue
                    if opcode == bin_format.f64_load:
                        # stack.add(Value.from_f64(utils.gen_symbolic_value(bin_format.f64,str(pc))))
                        stack.add(Value.from_f64(number.MemoryLoad.f64(
                            m.load(a,8))))
                        continue
                    if opcode == bin_format.i32_load8_s:
                        # stack.add(Value.from_i32(utils.gen_symbolic_value(bin_format.i32,f"i32_bv_mem_{pc}")))
                        stack.add(Value.from_i32(number.MemoryLoad.i8(
                            m.load(a,1))))
                        continue
                    if opcode == bin_format.i32_load8_u:
                        # stack.add(Value.from_i32(utils.gen_symbolic_value(bin_format.i32,f"i32_bv_mem_{pc}")))
                        stack.add(Value.from_i32(number.MemoryLoad.u8(
                            m.load(a,1))))
                        continue
                    if opcode == bin_format.i32_load16_s:
                        # stack.add(Value.from_i32(utils.gen_symbolic_value(bin_format.i32,f"i32_bv_mem_{pc}")))
                        stack.add(Value.from_i32(number.MemoryLoad.i16(
                            m.load(a,2))))
                        continue
                    if opcode == bin_format.i32_load16_u:
                        # stack.add(Value.from_i32(utils.gen_symbolic_value(bin_format.i32,f"i32_bv_mem_{pc}")))
                        stack.add(Value.from_i32(number.MemoryLoad.u16(
                            m.load(a,2))))
                        continue
                    if opcode == bin_format.i64_load8_s:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.i8(
                            m.load(a,1))))
                        continue
                    if opcode == bin_format.i64_load8_u:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.u8(
                            m.load(a,1))))
                        continue
                    if opcode == bin_format.i64_load16_s:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.i16(
                            m.load(a,2))))
                        continue
                    if opcode == bin_format.i64_load16_u:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.u16(
                            m.load(a,2))))
                        continue
                    if opcode == bin_format.i64_load32_s:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.i32(
                            m.load(a,4))))
                        continue
                    if opcode == bin_format.i64_load32_u:
                        # stack.add(Value.from_i64(utils.gen_symbolic_value(bin_format.i64,f"i64_bv_mem_{pc}")))
                        stack.add(Value.from_i64(number.MemoryLoad.u32(
                            m.load(a,4))))
                        continue
                    continue
                else:
                    a=utils.get_concrete_int(a)
                if a + bin_format.opcodes[opcode][2] > len(m.data):
                    print("out of bounds memory")
                    # stack.add(Value.from_i32)
                    global_vars.path_abort = True
                    # temp_stack = Stack()
                    # temp_stack.add(frame)
                    # if path_depth <= 0:
                    #     return branch_res, temp_stack, all_pc_states
                    # else:
                    #     return branch_res, temp_stack, all_pc_states
                    all_pc_states.extend(pc_state[:])
                    logger.infoln('Out of bounds memory access!')
                    break
                    # raise Exception('Out of bounds memory access!')
                if opcode == bin_format.i32_load:
                    # [TODO] a better method to process out of index
                    # print(a)
                    a = a if 0 <= a <= len(m.data) - 4 else randint(0, len(m.data) - 4)
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compmemoryX{a} CAT compmemoryX{a+1} CAT compmemoryX{a+2} CAT compmemoryX{a+3})")
                    #TODO: 每个memory变量存的是一个字节,[Con]CAT操作需要添加
                    #TODO: 这里可以加上，如果不是符号量的话，直接填入整数值的优化
                    stack.add(Value.from_i32(number.MemoryLoad.i32(m.data[a:a + 4])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load:
                    # [TODO] a better method to process out of index
                    a = a if 0 <= a <= len(m.data) - 8 else randint(0, len(m.data) - 8)
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compmemoryX{a} CAT compmemoryX{a+1} CAT compmemoryX{a+2} CAT compmemoryX{a+3} CAT compmemoryX{a+4} CAT compmemoryX{a+5} CAT compmemoryX{a+6} CAT compmemoryX{a+7})")
                    if utils.is_symbolic(m.data[a]):
                        tmp = z3.simplify(number.MemoryLoad.i64(m.data[a:a + 8]))
                        # print(f'cccaaa{tmp}')
                    else:
                        tmp = number.MemoryLoad.i64(m.data[a:a + 8])
                    stack.add(Value.from_i64(tmp))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue

                # [TODO] Using some approaches to implement float byte-store.
                if opcode == bin_format.f32_load:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compmemoryX{a} CAT compmemoryX{a+1} CAT compmemoryX{a+2} CAT compmemoryX{a+3})")
                    stack.add(Value.from_f32(number.LittleEndian.f32(m.data[a:a + 4])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_load:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compmemoryX{a} CAT compmemoryX{a+1} CAT compmemoryX{a+2} CAT compmemoryX{a+3} CAT compmemoryX{a+4} CAT compmemoryX{a+5} CAT compmemoryX{a+6} CAT compmemoryX{a+7})")
                    stack.add(Value.from_f64(number.LittleEndian.f64(m.data[a:a + 8])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue

                if opcode == bin_format.i32_load8_s:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT compmemoryX{a})")
                    #TODO: 符号扩展和无符号看成是一样的了，或许可以使用mkSignExt和mkZeroExt来修改
                    stack.add(Value.from_i32(number.MemoryLoad.i8(m.data[a:a + 1])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i32_load8_u:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT compmemoryX{a})")
                    stack.add(Value.from_i32(number.MemoryLoad.u8(m.data[a:a + 1])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i32_load16_s:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i32(number.MemoryLoad.i16(m.data[a:a + 2])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i32_load16_u:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i32(number.MemoryLoad.u16(m.data[a:a + 2])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load8_s:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.i8(m.data[a:a + 1])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load8_u:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.u8(m.data[a:a + 1])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load16_s:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.i16(m.data[a:a + 2])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load16_u:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.u16(m.data[a:a + 2])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load32_s:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a+3} CAT compmemoryX{a+2} CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.i32(m.data[a:a + 4])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.i64_load32_u:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT compmemoryX{a+3} CAT compmemoryX{a+2} CAT compmemoryX{a+1} CAT compmemoryX{a})")
                    stack.add(Value.from_i64(number.MemoryLoad.u32(m.data[a:a + 4])))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                continue

            if bin_format.i32_store <= opcode <= bin_format.i64_store32:
                # v is value, a is address
                v = stack.pop().n
                a = stack.pop().n + i.immediate_arguments[1]
                if utils.is_symbolic(a):
                    m = store.smems[module.memaddrs[0]]
                    a = z3.simplify(a)
                    if opcode == bin_format.i32_store:
                        m.store(a, 4 , number.MemoryStore.pack_i32(v))
                        continue
                    if opcode == bin_format.i64_store:
                        m.store(a, 8 , number.MemoryStore.pack_i64(v))
                        continue
                    if opcode == bin_format.f32_store:
                        m.store(a, 4 , number.MemoryStore.pack_f32(v))
                        continue
                    if opcode == bin_format.f64_store:
                        m.store(a, 8 , number.MemoryStore.pack_f64(v))
                        continue
                    if opcode == bin_format.i32_store8:
                        m.store(a, 1 , number.MemoryStore.pack_i8(v))
                        continue
                    if opcode == bin_format.i32_store16:
                        m.store(a, 2 , number.MemoryStore.pack_i16(v))
                        continue
                    if opcode == bin_format.i64_store8:
                        m.store(a, 1 , number.MemoryStore.pack_i8(v))
                        continue
                    if opcode == bin_format.i64_store16:
                        m.store(a, 2 , number.MemoryStore.pack_i16(v))
                        continue
                    if opcode == bin_format.i64_store32:
                        m.store(a, 4 , number.MemoryStore.pack_i32(v))
                        continue
                    continue

                else:
                    a=utils.get_concrete_int(a)
                if a + bin_format.opcodes[opcode][2] > len(m.data):
                    print("oom")
                    global_vars.path_abort = True
                    temp_stack = Stack()
                    temp_stack.add(frame)
                    # if path_depth <= 0:
                    #     return branch_res, temp_stack, all_pc_states
                    # else:
                    #     return branch_res, temp_stack, all_pc_states
                    # raise Exception('Out of bounds memory access!')
                    break
                if opcode == bin_format.i32_store:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(4)])
                    #TODO: ECT操作需要添加上,0表示取最低字节,>4之后的数字表示从最低位到这一位
                    m.data[a:a + 4] = number.MemoryStore.pack_i32(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.i64_store:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(8)])
                    m.data[a:a + 8] = number.MemoryStore.pack_i64(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    if utils.is_symbolic(v):
                        global_vars.add_dict_symbolic_address(v, a)
                    print("store at ",a)
                    continue

                if opcode == bin_format.f32_store:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(4)])
                    m.data[a:a + 4] = number.MemoryStore.pack_f32(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.f64_store:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(8)])
                    m.data[a:a + 8] = number.MemoryStore.pack_f64(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue

                if opcode == bin_format.i32_store8:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(1)])
                    m.data[a:a + 1] = number.MemoryStore.pack_i8(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.i32_store16:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(2)])
                    m.data[a:a + 2] = number.MemoryStore.pack_i16(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.i64_store8:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(1)])
                    m.data[a:a + 1] = number.MemoryStore.pack_i8(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.i64_store16:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(2)])
                    m.data[a:a + 2] = number.MemoryStore.pack_i16(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                if opcode == bin_format.i64_store32:
                    #primise.append(f"EqVar(compstackX{func_name}X{stack.frame_len} ADD {i.immediate_arguments[1]},{a})")
                    #primise.extend([f"SubstVar8(compmemoryX{a+i},compstackX{func_name}X{stack.frame_len+1} ECT {i})" for i in range(4)])
                    m.data[a:a + 4] = number.MemoryStore.pack_i32(v)
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    print("store at ",a)
                    continue
                continue
            if opcode == bin_format.current_memory:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{m.size})")
                stack.add(Value.from_i32(m.size))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue

            # [TODO] z3.If the grow size is a symbol, it could be difficult to execute. Current method
            #        is a simple random integer. There may exists bug.
            if opcode == bin_format.grow_memory:
                cur_size = m.size
                grow_size = stack.pop().n
                if not utils.is_all_real(grow_size) or grow_size > 100:
                    print("use random")
                    grow_size = randint(0, 100)
                m.grow(grow_size)
                stack.add(Value.from_i32(cur_size))
                continue
            continue

        if bin_format.i32_const <= opcode <= bin_format.f64_const:
            if opcode == bin_format.i32_const:
                # if i.immediate_arguments<0:
                #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 SUB {-i.immediate_arguments})")
                # else:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{i.immediate_arguments})")
                stack.add(Value.from_i32(i.immediate_arguments))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.i64_const:
                # if i.immediate_arguments<0:
                #     #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 SUB {-i.immediate_arguments})")
                # else:
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{i.immediate_arguments})")
                stack.add(Value.from_i64(i.immediate_arguments))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_const:
                # if i.immediate_arguments<0:
                #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},0 SUB {-i.immediate_arguments})")
                # else:
                #     #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{i.immediate_arguments})")
                stack.add(Value.from_f32(i.immediate_arguments))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_const:
                # if i.immediate_arguments<0:
                #     #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 SUB {-i.immediate_arguments})")
                # else:
                #     #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{i.immediate_arguments})")
                stack.add(Value.from_f64(i.immediate_arguments))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            continue
        if opcode == bin_format.i32_eqz:
            object_a = stack.pop()
            a = object_a.n
            if utils.is_all_real(a):
                computed = int(a == 0)
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
            else:
                computed = z3.If(a == 0, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},0)"\
                        #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},0)"\
                        #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
            object_c = Value.from_i32(computed)
            # detect the random number
            if id(object_a) in global_vars.block_number_id_list:
                global_vars.add_random_number_id(id(object_c))
            stack.add(object_c)
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if bin_format.i32_eq <= opcode <= bin_format.i32_geu:
            object_b = stack.pop()
            b = object_b.n
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = (id(object_a) in global_vars.block_number_id_list
                                  or id(object_b) in global_vars.block_number_id_list)

            
            if opcode == bin_format.i32_eq:
                if utils.is_all_real(a, b):
                    computed = int(a == b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a == b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_ne:
                if utils.is_all_real(a, b):
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a!=b)})")
                    computed = int(a != b)
                else:
                    computed = z3.simplify(z3.If(a != b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_lts:
                if utils.is_all_real(a, b):
                    computed = int(a < b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                    #TODO: 有符号和有符号的需要区别了
                else:
                    computed = z3.simplify(z3.If(a < b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                        #TODO: 需要添加SLEVAR
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_ltu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u32(a) < number.int2u32(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.ULT(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_gts:
                if utils.is_all_real(a, b):
                    computed = int(a > b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a > b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_gtu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u32(a) > number.int2u32(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.UGT(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_les:
                if utils.is_all_real(a, b):
                    computed = int(a <= b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a <= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"SLeVar(compstackX{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_leu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u32(a) <= number.int2u32(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.ULE(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_ges:
                if utils.is_all_real(a, b):
                    computed = int(a >= b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a >= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_geu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u32(a) >= number.int2u32(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.UGE(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion,primise_choices)
            continue

        if opcode == bin_format.i64_eqz:
            object_a = stack.pop()
            a = object_a.n
            if utils.is_all_real(a):
                computed = int(a == 0)
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
            else:
                computed = z3.simplify(z3.If(a == 0, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},0)"\
                        #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},0)"\
                        #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
            object_c = Value.from_i32(computed)
            # detect the random number
            if id(object_a) in global_vars.block_number_id_list:
                global_vars.add_random_number_id(id(object_c))
            stack.add(object_c)
            continue
        if bin_format.i64_eq <= opcode <= bin_format.i64_geu:
            object_b = stack.pop()
            b = object_b.n
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = (id(object_a) in global_vars.block_number_id_list
                                  or id(object_b) in global_vars.block_number_id_list)

            if opcode == bin_format.i64_eq:
                if utils.is_all_real(a, b):
                    computed = int(a == b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a == b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_ne:
                if utils.is_all_real(a, b):
                    computed = int(a != b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a != b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_lts:
                if utils.is_all_real(a, b):
                    computed = int(a < b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a < b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_ltu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u64(a) < number.int2u64(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.ULT(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_gts:
                if utils.is_all_real(a, b):
                    computed = int(a > b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a > b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_gtu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u64(a) > number.int2u64(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.UGT(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_les:
                if utils.is_all_real(a, b):
                    computed = int(a <= b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a <= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_leu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u64(a) <= number.int2u64(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.ULE(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_ges:
                if utils.is_all_real(a, b):
                    computed = int(a >= b)
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(a >= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"SLeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_geu:
                if utils.is_all_real(a, b):
                    computed = int(number.int2u64(a) >= number.int2u64(b))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{computed})")
                else:
                    computed = z3.simplify(z3.If(z3.UGE(a, b), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
            #write_rule(primise,action,conclusion)
            continue

        if bin_format.f32_eq <= opcode <= bin_format.f64_ge:
            b = stack.pop().n
            a = stack.pop().n
            if utils.is_all_real(a, b):
                if opcode == bin_format.f32_eq:
                    #primise.append(f"SubstVar32compstackX({func_name}X{stack.frame_len},{int(a == b)})")
                    stack.add(Value.from_i32(int(a == b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_ne:
                    #primise.append(f"SubstVar32compstackX({func_name}X{stack.frame_len},{int(a != b)})")
                    stack.add(Value.from_i32(int(a != b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_lt:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a < b)})")
                    stack.add(Value.from_i32(int(a < b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_gt:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a > b)})")
                    stack.add(Value.from_i32(int(a > b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_le:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a <= b)})")
                    stack.add(Value.from_i32(int(a <= b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_ge:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a >= b)})")
                    stack.add(Value.from_i32(int(a >= b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_eq:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a == b)})")
                    stack.add(Value.from_i32(int(a == b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_ne:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a != b)})")
                    stack.add(Value.from_i32(int(a != b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_lt:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a < b)})")
                    stack.add(Value.from_i32(int(a < b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_gt:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a > b)})")
                    stack.add(Value.from_i32(int(a > b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_le:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a <= b)})")
                    stack.add(Value.from_i32(int(a <= b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f64_ge:
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{int(a >= b)})")
                    stack.add(Value.from_i32(int(a >= b)))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
            else:
                if opcode == bin_format.f32_eq:
                    computed = z3.If(a == b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f32_ne:
                    computed = z3.If(a != b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f32_lt:
                    computed = z3.If(a < b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f32_gt:
                    computed = z3.If(a > b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f32_le:
                    computed = z3.If(a <= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion)
                    continue
                if opcode == bin_format.f32_ge:
                    computed = z3.If(a >= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_eq:
                    computed = z3.If(a == b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            # #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            # #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_ne:
                    computed = z3.If(a != b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"NeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            # #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            # #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_lt:
                    computed = z3.If(a < b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_gt:
                    computed = z3.If(a > b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                            #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_le:
                    computed = z3.If(a <= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    # #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    # #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    # #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
                if opcode == bin_format.f64_ge:
                    computed = z3.If(a >= b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
                    # #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},1)"])
                    # #primise_choices.append([f"EqVar(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len+1})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    # #primise_choices.append([f"LeVar(compstackX{func_name}X{stack.frame_len+1},compstackX{func_name}X{stack.frame_len})"\
                    #         #,f"SubstVar32(compstackX{func_name}X{stack.frame_len},0)"])
                    stack.add(Value.from_i32(computed))
                    #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                    #write_rule(primise,action,conclusion,primise_choices)
                    continue
            continue

        # [TODO] Difficulty to symbolic execution.
        if bin_format.i32_clz <= opcode <= bin_format.i32_popcnt:
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = id(object_a) in global_vars.block_number_id_list
            if opcode == bin_format.i32_clz:
                if utils.is_all_real(a):
                    c = 0
                    while c < 32 and (a & 0x80000000) == 0:
                        c += 1
                        a *= 2
                else:

                    c = 0
                object_c = Value.from_i32(c)
                stack.add(object_c)

            elif opcode == bin_format.i32_ctz:
                if utils.is_all_real(a):
                    c = 0
                    while c < 32 and (a % 2) == 0:
                        c += 1
                        a /= 2
                else:
                    c = 0
                object_c = Value.from_i32(c)
                stack.add(object_c)

            elif opcode == bin_format.i32_popcnt:
                if utils.is_all_real(a):
                    c = 0
                    for i in range(32):
                        if 0x1 & a:
                            c += 1
                        a //= 2
                else:
                    c = 0
                object_c = Value.from_i32(c)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            continue

        if bin_format.i32_add <= opcode <= bin_format.i32_rotr:
            object_b = stack.pop()
            b = object_b.n
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = (id(object_a) in global_vars.block_number_id_list
                                  or id(object_b) in global_vars.block_number_id_list)

            if opcode in [
                bin_format.i32_divs,
                bin_format.i32_divu,
                bin_format.i32_rems,
                bin_format.i32_remu,
            ]:
                if utils.is_all_real(b) and b == 0:
                    logger.println('Integer divide by zero!')
                    b = 1
                elif not utils.is_all_real(b):
                    solver.push()
                    solver.add(z3.Not(b == 0))
                    find_symbolic_in_solver(solver)
                    if utils.check_sat(solver) == z3.unsat:
                        logger.println('Integer divide by zero!')
                        b = 1
                    solver.pop()
            if opcode == bin_format.i32_add:
                if utils.is_all_real(a, b):
                    computed = number.int2i32(a + b)
                else:
                    computed = z3.simplify(a + b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<31)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<31)-1))
                    if 'addr' not in str(computed) and 'input' in str(computed) and utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ADD compstackX{func_name}X{stack.frame_len+1})")
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_sub:
                if utils.is_all_real(a, b):
                    computed = number.int2i32(a - b)
                else:
                    computed = z3.simplify(a - b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<31)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<31)-1))
                    # if utils.check_sat(solver)==z3.sat:
                    if 'addr' not in str(computed) and 'input' in str(computed) and  utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SUB compstackX{func_name}X{stack.frame_len+1})")
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_mul:
                if utils.is_all_real(a, b):
                    computed = number.int2i32(a * b)
                else:
                    computed = z3.simplify(a * b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<31)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<31)-1))
                    if 'addr' not in str(computed) and 'input' in str(computed) and  utils.check_sat(solver)==z3.sat:
                    # if utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} MUL compstackX{func_name}X{stack.frame_len+1})")
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_divs:
                if utils.is_all_real(a, b):
                    if a == 0x8000000 and b == -1:
                        print('Integer overflow!')
                        # raise Exception('Integer overflow!')
                    computed = number.idiv_s(a, b)
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    solver.push()
                    solver.add((a / b) < 0)
                    find_symbolic_in_solver(solver)
                    sign = -1 if utils.check_sat(solver) == z3.sat else 1
                    a, b = utils.sym_abs(a), utils.sym_abs(b)
                    computed = z3.simplify(sign * (a / b))
                    solver.pop()
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SDIV compstackX{func_name}X{stack.frame_len+1})")
                    #TODO: 需要添加SDIV操作
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_divu:
                if utils.is_all_real(a, b):
                    computed = number.int2i32(number.int2u32(a) // number.int2u32(b))
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    computed = z3.simplify(z3.UDiv(a, b))
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} DIV compstackX{func_name}X{stack.frame_len+1})")
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_rems:
                if utils.is_all_real(a, b):
                    computed = number.irem_s(a, b)
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    if is_blockchain_state(a) or is_blockchain_state(b):
                        action.append("Block_State()")
                        global_vars.call_block_state=True
                        #print("block info depend vulneralbility find")
                    solver.push()
                    solver.add(a < 0)
                    find_symbolic_in_solver(solver)
                    sign = -1 if utils.check_sat(solver) == z3.sat else 1
                    solver.pop()
                    a, b = utils.sym_abs(a), utils.sym_abs(b)
                    computed = z3.simplify(sign * (a % b))
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SREM compstackX{func_name}X{stack.frame_len+1})")
                    #TODO: 需要添加SREM操作
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_remu:
                if utils.is_all_real(a, b):
                    computed = number.int2i32(number.int2u32(a) % number.int2u32(b))
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    computed = z3.simplify(z3.URem(a, b))
                    if is_blockchain_state(a) or is_blockchain_state(b):
                        action.append("Block_State()")
                        global_vars.call_block_state=True
                        #print("block info depend vulneralbility find")
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} REM compstackX{func_name}X{stack.frame_len+1})")
                    #TODO: 需要添加REM操作,mkBvurem
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_and:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} AND compstackX{func_name}X{stack.frame_len+1})")
                computed = a & b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                    #TODO: 需要添加AND操作
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_or:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} OR compstackX{func_name}X{stack.frame_len+1})")
                computed = a | b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                    #TODO: 需要添加OR操作
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_xor:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} XOR compstackX{func_name}X{stack.frame_len+1})")
                    #TODO: 需要添加XOR操作
                computed = a ^ b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_shl:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHL compstackX{func_name}X{stack.frame_len+1})")
                    #TODO: 需要添加SHL操作
                if utils.is_all_real(a, b):
                    computed = number.int2i32(a << (b % 0x20))
                else:
                    computed = z3.simplify(
                        a << (b & 0x1F))  # [TODO] Two implementation " & 0x1F" and " % 0x20" are equvalent.
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_shrs:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHRS compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = a >> (b % 0x20)
                else:
                    computed = z3.simplify(a >> (b & 0x1F))
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_shru:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHR compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2u32(a) >> (b % 0x20)
                else:
                    computed = z3.simplify(z3.LShR(a, b & 0x1F))
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_rotl:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ROTL compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i32(number.rotl_u32(a, b))
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    computed = z3.simplify(z3.RotateLeft(a, b))
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            elif opcode == bin_format.i32_rotr:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ROTR compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i32(number.rotr_u32(a, b))
                else:
                    a, b = utils.to_symbolic(a, 32), utils.to_symbolic(b, 32)
                    computed = z3.simplify(z3.RotateRight(a, b))
                object_c = Value.from_i32(computed)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            new_tmr_vars=gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1)
            #conclusion.append(new_tmr_vars)
            #write_rule(primise,action,conclusion)
            # if global_vars.gen_overflow and oaction:
                #write_rule([new_tmr_vars]+oprimise,oaction,["Overflow_End()"])
            continue

        # [TODO] Diffculty to find an approach to implement the instruction.
        if bin_format.i64_clz <= opcode <= bin_format.i64_popcnt:
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = True if id(object_a) in global_vars.block_number_id_list else False

            if opcode == bin_format.i64_clz:
                if a < 0:
                    stack.add(object_a)
                    continue
                c = 1
                while c < 63 and (a & 0x4000000000000000) == 0:
                    c += 1
                    a *= 2
                object_c = Value.from_i64(c)
                stack.add(object_c)

            elif opcode == bin_format.i64_ctz:
                c = 0
                while c < 64 and (a % 2) == 0:
                    c += 1
                    a /= 2
                object_c = Value.from_i64(c)
                stack.add(object_c)

            elif opcode == bin_format.i64_popcnt:
                c = 0
                for i in range(64):
                    if 0x1 & a:
                        c += 1
                    a //= 2
                object_c = Value.from_i64(c)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            continue

        if opcode >= bin_format.i64_add and opcode <= bin_format.i64_rotr:
            object_b = stack.pop()
            b = object_b.n
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = (id(object_a) in global_vars.block_number_id_list
                                  or id(object_b) in global_vars.block_number_id_list)

            if opcode in [
                bin_format.i64_divs,
                bin_format.i64_divu,
                bin_format.i64_rems,
                bin_format.i64_remu,
            ]:
                if utils.is_all_real(b) and b == 0:
                    logger.println('Integer divide by zero!')
                    b = 1
                elif not utils.is_all_real(b):
                    solver.push()
                    solver.add(z3.Not(b == 0))
                    find_symbolic_in_solver(solver)
                    if utils.check_sat(solver) == z3.unsat:
                        logger.println('Integer divide by zero!')
                        b = 1
                    solver.pop()
            if opcode == bin_format.i64_add:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ADD compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(a + b)
                else:
                    computed = z3.simplify(a + b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<63)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<63)-1))
                    if utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_sub:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SUB compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(a - b)
                else:
                    computed = z3.simplify(a - b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<63)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<63)-1))
                    if utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_mul:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} MUL compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(a * b)
                else:
                    computed = z3.simplify(a * b)
                    # if global_vars.gen_overflow:
                    #     oprimise=[f"EqVar(compstackX{func_name}X{stack.frame_len},{(1<<63)-1})"]
                    #     oaction=["OverFlow()"]
                    solver.push()
                    solver.add(computed==((1<<63)-1))
                    if utils.check_sat(solver)==z3.sat:
                        global_vars.overflow=True
                        print("calc overflow")
                    solver.pop()
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_divs:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SDIV compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    if a == 0x80000000 and b == -1:
                        print('Integer overflow!')
                        # raise Exception('Integer overflow!')
                    computed = number.idiv_s(a, b)
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    solver.push()
                    solver.add((a / b) < 0)
                    find_symbolic_in_solver(solver)
                    sign = -1 if utils.check_sat(solver) == z3.sat else 1
                    a, b = utils.sym_abs(a), utils.sym_abs(b)
                    computed = z3.simplify(sign * (a / b))
                    solver.pop()
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_divu:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} DIV compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(number.int2u64(a) // number.int2u64(b))
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    computed = z3.simplify(z3.UDiv(a, b))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_rems:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} REMS compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.irem_s(a, b)
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    solver.push()
                    solver.add(a < 0)
                    find_symbolic_in_solver(solver)
                    sign = -1 if utils.check_sat(solver) == z3.sat else 1
                    solver.pop()
                    a, b = utils.sym_abs(a), utils.sym_abs(b)
                    computed = z3.simplify(sign * (a % b))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_remu:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} REM compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i32(number.int2u64(a) % number.int2u64(b))
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    computed = z3.simplify(z3.URem(a, b))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_and:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} AND compstackX{func_name}X{stack.frame_len+1})")
                computed = a & b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_or:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} OR compstackX{func_name}X{stack.frame_len+1})")
                computed = a | b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_xor:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} XOR compstackX{func_name}X{stack.frame_len+1})")
                computed = a ^ b
                if z3.is_expr(computed):
                    computed = z3.simplify(computed)
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_shl:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHL compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(a << (b % 0x40))
                else:
                    computed = z3.simplify(a << (b & 0x3F))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_shrs:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHRS compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = a >> (b % 0x40)
                else:
                    computed = z3.simplify(a >> (b & 0x3F))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_shru:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHR compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2u64(a) >> (b % 0x40)
                elif utils.is_all_real(a) and utils.is_symbolic(b):
                    computed = z3.simplify(number.int2u64(a) >> (b & 0x3F))
                else:
                    b = utils.to_symbolic(b, 64)
                    computed = z3.simplify(z3.LShR(a, b & 0x3F))
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} SHR compstackX{func_name}X{stack.frame_len+1})")
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_rotl:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ROTL compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(number.rotr_u64(a, b))
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    computed = z3.simplify(z3.RotateLeft(a, b))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            elif opcode == bin_format.i64_rotr:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},compstackX{func_name}X{stack.frame_len} ROTR compstackX{func_name}X{stack.frame_len+1})")
                if utils.is_all_real(a, b):
                    computed = number.int2i64(number.rotr_u64(a, b))
                else:
                    a, b = utils.to_symbolic(a, 64), utils.to_symbolic(b, 64)
                    computed = z3.simplify(z3.RotateRight(a, b))
                object_c = Value.from_i64(computed)
                stack.add(object_c)

            if random_number_flag:
                global_vars.add_random_number_id(id(object_c))
            #new_tmr_vars=gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1)
            #conclusion.append(new_tmr_vars)
            #write_rule(primise,action,conclusion)
            # if global_vars.gen_overflow and oaction:
                #write_rule([new_tmr_vars]+oprimise,oaction,["Overflow_End()"])
            continue

        # [TODO] float number problems.
        if bin_format.f32_abs <= opcode <= bin_format.f32_sqrt:
            a = stack.pop().n
            if opcode == bin_format.f32_abs:
                if utils.is_all_real(a):
                    stack.add(Value.from_f32(abs(a)))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{abs(a)})")
                else:
                    stack.add(Value.from_f32(z3.fpAbs(a)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_neg:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{-a})")
                stack.add(Value.from_f32(-a))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            # [TODO]: the follow 3 op cannot implement at present
            if opcode == bin_format.f32_ceil:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{math.ceil(a)})")
                stack.add(Value.from_f32(math.ceil(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_floor:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{math.floor(a)})")
                stack.add(Value.from_f32(math.floor(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_trunc:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{math.trunc(a)})")
                stack.add(Value.from_f32(math.trunc(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_nearest:  # depend on f32_ceil
                ceil = math.ceil(a)
                if ceil - a <= 0.5:
                    r = ceil
                else:
                    r = ceil - 1
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{r})")
                stack.add(Value.from_f32(r))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_sqrt:
                if utils.is_all_real(a):
                    stack.add(Value.from_f32(math.sqrt(a)))
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{r})")
                else:
                    stack.add(Value.from_f32(z3.fpSqrt(a)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            continue
        if bin_format.f32_add <= opcode <= bin_format.f32_copysign:
            b = stack.pop().n
            a = stack.pop().n
            if opcode == bin_format.f32_add:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{a + b})")
                stack.add(Value.from_f32(a + b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_sub:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{a - b})")
                stack.add(Value.from_f32(a - b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_mul:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{a * b})")
                stack.add(Value.from_f32(a * b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_div:
                if utils.is_all_real(b) and abs(b - 0.0) < 1e-10:
                    b = 1.0
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{a / b})")
                stack.add(Value.from_f32(a / b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_min:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{r})")
                if utils.is_all_real(a, b):
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{min(a, b)})")
                    stack.add(Value.from_f32(min(a, b)))
                else:
                    stack.add(Value.from_f32(z3.fpMin(a, b)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_max:
                if utils.is_all_real(a, b):
                    #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{max(a, b)})")
                    stack.add(Value.from_f32(max(a, b)))
                else:
                    stack.add(Value.from_f32(z3.fpMax(a, b)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f32_copysign:
                if utils.is_all_real(a, b):
                    stack.add(Value.from_f32(math.copysign(a, b)))
                elif utils.is_all_real(b):
                    stack.add(Value.from_f32(z3.fpAbs(a) * (1 if b > 0 else -1)))
                elif utils.is_all_real(a):
                    stack.add(Value.from_f32(abs(a) * z3.If(b > 0, z3.BitVecVal(1, 32), z3.BitVecVal(-1, 32))))
                else:
                    stack.add(Value.from_f32(z3.fpAbs(a) * z3.If(b > 0, z3.BitVecVal(1, 32), z3.BitVecVal(-1, 32))))
                continue
            continue
        if bin_format.f64_abs <= opcode <= bin_format.f64_sqrt:
            a = stack.pop().n
            if opcode == bin_format.f64_abs:
                if utils.is_all_real(a):
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{abs(a)})")
                    stack.add(Value.from_f64(abs(a)))
                else:
                    stack.add(Value.from_f64(z3.fpAbs(a)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_neg:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{-a})")
                stack.add(Value.from_f64(-a))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            # [TODO]: cannot implement at present
            if opcode == bin_format.f64_ceil:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{math.ceil(a)})")
                stack.add(Value.from_f64(math.ceil(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_floor:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{math.floor(a)})")
                stack.add(Value.from_f64(math.floor(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_trunc:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{math.trunc(a)})")
                stack.add(Value.from_f64(math.trunc(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_nearest:
                ceil = math.ceil(a)
                if ceil - a <= 0.5:
                    r = ceil
                else:
                    r = ceil - 1
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{r})")
                stack.add(Value.from_f64(r))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_sqrt:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{math.sqrt(a)})")
                stack.add(Value.from_f64(math.sqrt(a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            continue
        if bin_format.f64_add <= opcode <= bin_format.f64_copysign:
            b = stack.pop().n
            a = stack.pop().n
            if opcode == bin_format.f64_add:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{a + b})")
                stack.add(Value.from_f64(a + b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_sub:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{a - b})")
                stack.add(Value.from_f64(a - b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_mul:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{a * b})")
                stack.add(Value.from_f64(a * b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_div:
                if utils.is_all_real(b) and abs(b - 0.0) < 1e-10:
                    logger.println('float division by zero!')
                    b = 1.0
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{a / b})")
                stack.add(Value.from_f64(a / b))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_min:
                if utils.is_all_real(a, b):
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{min(a, b)})")
                    stack.add(Value.from_f64(min(a, b)))
                else:
                    stack.add(Value.from_f64(z3.fpMin(a, b)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_max:
                if utils.is_all_real(a, b):
                    #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},{max(a, b)})")
                    stack.add(Value.from_f64(max(a, b)))
                else:
                    stack.add(Value.from_f64(z3.fpMax(a, b)))
                    # print_red("error")
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.f64_copysign:
                if utils.is_all_real(a, b):
                    stack.add(Value.from_f64(math.copysign(a, b)))
                elif utils.is_all_real(b):
                    stack.add(Value.from_f64(z3.fpAbs(a) * (1 if b > 0 else -1)))
                elif utils.is_all_real(a):
                    stack.add(Value.from_f64(abs(a) * z3.If(b > 0, z3.BitVecVal(1, 32), z3.BitVecVal(-1, 32))))
                else:
                    stack.add(Value.from_f64(z3.fpAbs(a) * z3.If(b > 0, z3.BitVecVal(1, 32), z3.BitVecVal(-1, 32))))
                continue
            continue
        if bin_format.i32_wrap_i64 <= opcode <= bin_format.f64_promote_f32:
            object_a = stack.pop()
            a = object_a.n

            # detect the random number
            random_number_flag = id(object_a) in global_vars.block_number_id_list

            if opcode in [
                bin_format.i32_trunc_sf32,
                bin_format.i32_trunc_uf32,
                bin_format.i32_trunc_sf64,
                bin_format.i32_trunc_uf64,
                bin_format.i64_trunc_sf32,
                bin_format.i64_trunc_uf32,
                bin_format.i64_trunc_sf64,
                bin_format.i64_trunc_uf64,
            ]:
                if utils.is_all_real(a) and math.isnan(a):
                    raise Exception('Invalid conversion to integer!')
            if opcode == bin_format.i32_wrap_i64:
                #primise.append(f"SubstVar32(compstackX{func_name}X{stack.frame_len},{a})")
                stack.add(Value.from_i32(number.int2i32(a)))
                continue
            if opcode == bin_format.i32_trunc_sf32:
                if utils.is_all_real(a):
                    if a > 2 ** 31 - 1 or a < -2 ** 32:
                        raise Exception('Integer overflow!')
                    stack.add(Value.from_i32(int(a)))
                else:
                    stack.add(Value.from_i32(0))
                continue
            if opcode == bin_format.i32_trunc_uf32:
                if utils.is_all_real(a):
                    if a > 2 ** 32 - 1 or a < -1:
                        raise Exception('Integer overflow!')
                    stack.add(Value.from_i32(int(a)))
                else:
                    stack.add(Value.from_i32(0))
                continue
            if opcode == bin_format.i32_trunc_sf64:
                if utils.is_all_real(a):
                    if a > 2 ** 31 - 1 or a < -2 ** 32:
                        raise Exception('Integer overflow!')
                    stack.add(Value.from_i32(int(a)))
                else:
                    stack.add(Value.from_i32(0))
                continue
            if opcode == bin_format.i32_trunc_uf64:
                if utils.is_all_real(a):
                    if a >= 2 ** 32 - 1 or a < -1:
                        raise Exception('Integer overflow!')
                    stack.add(Value.from_i32(int(a)))
                else:
                    stack.add(Value.from_i32(0))
                continue
            if opcode == bin_format.i64_extend_si32:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT compstackX{func_name}X{stack.frame_len})")
                if utils.is_all_real(a):
                    stack.add(Value.from_i64(a))
                else:
                    stack.add(Value.from_i64(z3.SignExt(a, 32)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.i64_extend_ui32:
                #primise.append(f"SubstVar64(compstackX{func_name}X{stack.frame_len},0 CAT 0 CAT 0 CAT 0 CAT compstackX{func_name}X{stack.frame_len})")
                if utils.is_all_real(a):
                    stack.add(Value.from_i64(number.int2u32(a)))
                else:
                    stack.add(Value.from_i64(z3.ZeroExt(32, a)))
                #conclusion.append(gen_tmr_vars(store, frame, stack.frame_len, module, func_name, pc+1))
                #write_rule(primise,action,conclusion)
                continue
            if opcode == bin_format.i64_trunc_sf32:
                if a > 2 ** 63 - 1 or a < -2 ** 63:
                    raise Exception('Integer overflow!')
                stack.add(Value.from_i64(int(a)))
                continue
            if opcode == bin_format.i64_trunc_uf32:
                if a > 2 ** 64 - 1 or a < -1:
                    raise Exception('Integer overflow!')
                stack.add(Value.from_i64(int(a)))
                continue
            if opcode == bin_format.i64_trunc_sf64:
                stack.add(Value.from_i64(int(a)))
                continue
            if opcode == bin_format.i64_trunc_uf64:
                if a < -1:
                    raise Exception('Integer overflow!')
                stack.add(Value.from_i64(int(a)))
                continue
            if opcode == bin_format.f32_convert_si32:
                stack.add(Value.from_f32(a))
                continue
            if opcode == bin_format.f32_convert_ui32:
                stack.add(Value.from_f32(number.int2u32(a)))
                continue
            if opcode == bin_format.f32_convert_si64:
                stack.add(Value.from_f32(a))
                continue
            if opcode == bin_format.f32_convert_ui64:
                stack.add(Value.from_f32(number.int2u64(a)))
                continue
            if opcode == bin_format.f32_demote_f64:
                stack.add(Value.from_f32(a))
                continue
            if opcode == bin_format.f64_convert_si32:
                stack.add(Value.from_f64(a))
                continue
            if opcode == bin_format.f64_convert_ui32:
                stack.add(Value.from_f64(number.int2u32(a)))
                continue
            if opcode == bin_format.f64_convert_si64:
                stack.add(Value.from_f64(a))
                continue
            if opcode == bin_format.f64_convert_ui64:
                stack.add(Value.from_f64(number.int2u64(a)))
                continue
            if opcode == bin_format.f64_promote_f32:
                stack.add(Value.from_f64(a))
                continue
            continue
        if bin_format.i32_reinterpret_f32 <= opcode <= bin_format.f64_reinterpret_i64:
            a = stack.pop().n
            if opcode == bin_format.i32_reinterpret_f32:
                stack.add(Value.from_i32(number.f322i32(a)))
                continue
            if opcode == bin_format.i64_reinterpret_f64:
                stack.add(Value.from_i64(number.f642i64(a)))
                continue
            if opcode == bin_format.f32_reinterpret_i32:
                stack.add(Value.from_f32(number.i322f32(a)))
                continue
            if opcode == bin_format.f64_reinterpret_i64:
                stack.add(Value.from_f64(number.i642f64(a)))
                continue
            continue

    return [stack.pop() for _ in range(frame.arity)][::-1], stack, all_pc_states
