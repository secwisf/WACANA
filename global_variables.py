#!/usr/bin/python3
# -*- coding: utf-8 -*-

"""
The module is the global variables store the bug count and execution path and etc.
For simplicity, it only contain the unique object global_variables_instance of class
GlobalVariables.
"""
import utils
import z3
import logging

class GlobalVariables:
    def __init__(self, contract_type: str = 'eos', lvl: int = 0, simple: bool = False, output_file:str=None,storage=None,contractName='hello',db_store_id=0,log_count=0,db_update_id=0,pc_sets=set(),pc_cnts=set(),db_remove_id=0,missing_permissions=False,rollback=False ,overflow=False,overflow_vul=False,block_information_depend=False,sensitive_op=False,pathOfHookedContract='./rt/',user_name='hello') -> None:
        # program counter
        self.pc = 0

        # global path conditions and path results
        self.path_conditions_and_results = {"path_conditions": [], "results": []}

        # last stack
        self.last_stack = []

        # mark the type of smart contract
        self.contract_type = contract_type

        # the bug flags variables
        # block dependency bugs
        self.block_dependency_count = 0
        self.tapos_block_function_addr = list()
        self.block_number_id_list = list()
        self.send_token_function_addr = list()

        # ethereum delegate call bugs
        self.ethereum_delegate_call = 0
        self.call_delegate_addr = list()

        # ethereum greedy bugs
        self.ethereum_greedy = 0
        self.main_function_address = None
        self.get_call_value_addr = list()
        self.cannot_send_ETH = False
        self.ETH_payable_function_address_set = set()

        # ethereum expensive fallback bugs
        self.ethereum_revert_addr = list()
        self.expensive_fallback = 0
        self.max_gas_cost = 0

        # mode flag
        self.location_mode = False
        self.fake_detection_mode = False
        self.forged_detection_mode = False

        # forged transfer notification bugs
        self.vm = None
        self.forged_transfer_notification_count = 0
        self.found_to_check = False
        self.transfer_function_index = None
        self.transfer_function_address = None
        self.transfer_function_params = None
        self.self_locals = set()
        self.to_locals = set()
        self.unpack_locals = set()
        self.to_offset = None
        self.contract_name_int64 = None
        self.eosio_assert_addrs = set()
        self.action_data_size_addrs = set()
        self.read_action_data_addrs = set()
        self.require_auth_addrs = set()
        self.shadow_ranges = set()

        # fake eos transfer bugs
        self.apply_function_address = None
        self.apply_params = []
        self.fake_eos_transfer_count = 0
        self.data_addr_dict = {}
        self.eosio_token_locals = set()

        # loop depth limit
        self.LOOP_DEPTH_LIMIT = 500#路径中常亮分支指令个数
        # self.LOOP_DEPTH_LIMIT = 100#路径中常亮分支指令个数
        self.BRANCH_DEPTH_LIMIT = 10#路径中符号量分支指令个数
        # self.BRANCH_DEPTH_LIMIT = 10#路径中符号量分支指令个数
        self.CALL_DEPTH_LIMIT = 5

        # unreachable count
        self.unreachable_count = 0

        # jugde if simple execute
        self.is_simple = simple

        # offset of library func in wasm and library 
        self.library_offset = 0

        # flag to simulate eth.callDataCopy
        self.flag_callDataCopy = 0
        self.num_callDataCopy = 0

        # flag to simulate eth.getCallValue
        self.flag_getCallValue = 0
        self.flag_getCallValue_in_function = False
        self.num_getCallValue = 0

        # flag to simulate eth.revert
        self.flag_revert = 0

        # flag to simulate eth.getCallDataSize, 0 -> symbolic, 1 -> real(>4)
        self.flag_getCallDataSize = 0

        # flag to simulate eth.getCaller
        self.flag_getCaller = 0
        self.num_getCaller = 0

        # flag to simulate keccak256
        self.flag_keccak256 = 0
        self.num_keccak256 = 0

        # flag to simulate eth.getExternalBalance
        self.flag_getExternalBalance = 0
        self.num_getExternalBalance = 0


        # flag to detect mishandled exception
        self.flag_call_mishandled_exception = 0
        self.call_symbolic_ret = dict()

        # simulate $div and $mul
        self.num_div = 0
        self.num_mul = 0


        # simulate eth.storageLoad
        self.num_storageLoad = 0

        # sum of pc 
        self.sum_pc = list()
        self.cur_sum_pc = 0

        self.lvl = lvl

        self.list_func = list()
        self.len_list_func = 0

        # to manage symbolic_num
        self.flag_num_host = 0
        self.flag_num_wasm = 0

        # update check block dependency
        self.dict_block_solver = dict()

        # Record the initial memory location of the symbol value
        # Also record the converted symbol value
        self.dict_symbolic_address = dict()

        # save symbolic of eth.storageStore, use it to detect reentrancy
        self.list_storageStore = list()

        self.ethereum_reentrancy_detection = 0

        self.skip_call = False
        self.output_file = output_file
        self.func_name_stack = []
        self.should_write_rule=False
        self.gen_overflow = True
        # self.gvar_cnt_stack = []
        self.call_authenticate=False
        self.call_block_state=False
        self.get_block_state=False
        self.missing_permissions = missing_permissions
        self.rollback = rollback
        self.overflow = overflow
        self.overflow_vul = overflow_vul
        self.block_information_depend=block_information_depend
        self.sensitive_op=sensitive_op
        self.function_callcnt_map = {}
        self.pc_sets = pc_sets
        self.pc_cnts = pc_cnts
        
        #fuzz config
        logging.basicConfig(level = logging.DEBUG,
                    format = '%(name)s - %(levelname)s - %(message)s',
                    filename='.logger.log')
        self.logger = logging.getLogger()
        self.nodeosExecutable = 'nodeos'
        self.eosFilePath=''
        self.cleosExecutable='cleos'
        self.eosioTokenPublicKey = 'EOS6MRyAjQq8ud7hVNYcfnVPJqcVpscN5So8BhtHuGYqET5GDW5CV' 
        self.aPublicKey =          'EOS6MRyAjQq8ud7hVNYcfnVPJqcVpscN5So8BhtHuGYqET5GDW5CV'
        self.aPasswordToKeosd = 'PW5JJCpLY8BpYsHVYqRMn216Q1KLYSYvfsdNqDm2GGduzsu8XPaiL'
        self.eosioTokenContract = './agents/eosio.token/'
        self.atkforgContract = './agents/tokenlock'
        self.atknotiContract = './agents/atknoti'
        self.logPath = '/home/szh/LOGS'

        self.atkreroContract = './agents/atkrero'

        self.atkforgContractSource = './agents/atkforg/atkforg.cpp'
        self.atkforgContractBinary = './agents/atkforg/atkforg.wasm'


        self.forgedNotificationAgentName = "atkforg"
        self.forgedNotificationTokenFromName = "pokpokpokpok"#"atkforgfrom"#
        # {1: ['nkpaymentcap', 'pickowngames', 'eosbetdice11'], 6: ['pickowngames']}
        # gambaccarats_3-9'
        # 'epsdcclassic', 'gambaccarats_3-9', 'pickowngames', 'eosbetdice11' # pokpok
        # result: epsdcclassic gambaccarats_3-9 pickowngames nkpaymentcap eosbetdice11


        self.fakeTransferAgentName ="fake.token"  # "122icgw5c12s"# 
        self.fakeTransferUserName = 'fakeosio'
        self.testEOSTokenFromName = "testeosfrom"
        self.contractName=contractName
        self.user_name=user_name
        self.pathOfHookedContract=pathOfHookedContract
        self.plogPath = self.pathOfHookedContract+'/log2.txt'

        self.storage = storage

        self.db_store_id = db_store_id
        self.db_update_id = db_update_id
        self.db_remove_id=db_remove_id
        self.log_count= log_count
        self.path_abort=False
        self.test_argument=list()
        self.test_argument_type=None
        self.cut_on_unsat=True


    def re_init(self) -> None:
        print("re_init")
        print("permission check",self.missing_permissions)
        self.__init__(self.contract_type, self.lvl, self.is_simple,self.output_file,self.storage,self.contractName,self.db_store_id,self.log_count,self.db_update_id,self.pc_sets,self.pc_cnts,self.db_remove_id,self.missing_permissions ,self.rollback ,self.overflow,self.overflow_vul,self.block_information_depend,self.sensitive_op,self.pathOfHookedContract,self.user_name)

    def clear_count(self) -> None:
        self.block_dependency_count = 0
        self.fake_eos_transfer_count = 0
        self.ethereum_delegate_call = 0
        self.forged_transfer_notification_count = 0

        self.vm = None
        self.found_to_check = False
        self.transfer_function_index = None
        self.self_locals = set()
        self.to_locals = set()
        self.unpack_locals = set()
        self.to_offset = None
        self.contract_name_int64 = None
        self.eosio_assert_addrs = set()
        self.action_data_size_addrs = set()
        self.read_action_data_addrs = set()
        self.require_auth_addrs = set()
        self.shadow_ranges = set()

        self.apply_function_address = None

    def sym_exec(self):
        self.fake_detection_mode = False
        self.forged_detection_mode = False
        self.location_mode = False

    def locate(self):
        self.location_mode = True

    def fake_detect(self):
        self.fake_detection_mode = True

    def forged_detect(self):
        self.forged_detection_mode = True

    @property
    def detection_mode(self):
        return self.fake_detection_mode or self.forged_detection_mode

    def set_name_int64(self, name):
        self.contract_name_int64 = utils.eos_abi_to_int(name)

    def add_cond_and_results(self, path_condition: list, left_branch_res: list) -> None:
        self.path_conditions_and_results["path_conditions"].append(path_condition[:])
        self.path_conditions_and_results["results"].append(left_branch_res[:])

    def add_tapos_block_function_addr(self, address: int) -> None:
        self.tapos_block_function_addr.append(address)

    def add_random_number_id(self, number_id: int) -> None:
        self.block_number_id_list.append(number_id)

    def add_send_token_function_addr(self, address: int) -> None:
        self.send_token_function_addr.append(address)

    def add_call_delegate_addr(self, address: int) -> None:
        self.call_delegate_addr.append(address)

    def add_revert_addr(self, address: int) -> None:
        self.ethereum_revert_addr.append(address)

    def add_get_call_value_addr(self, address: int) -> None:
        self.get_call_value_addr.append(address)

    def set_main_function_addr(self, address: int) -> None:
        self.main_function_address = address

    def set_apply_function_addr(self, address: int) -> None:
        self.apply_function_address = address

    def find_forged_notification(self):
        self.forged_transfer_notification_count = 1

    def find_block_dependence(self) -> None:
        self.block_dependency_count += 1

    def find_fake_eos_transfer(self) -> None:
        self.fake_eos_transfer_count = 1

    def find_ethereum_delegate_call(self) -> None:
        self.ethereum_delegate_call += 1

    def find_ethereum_greedy(self) -> None:
        self.ethereum_greedy = 1

    def add_flag_callDataCopy(self) -> None:
        self.flag_callDataCopy += 1

    def clear_flag_callDataCopy(self) -> None:
        self.flag_callDataCopy = 0

    def add_num_callDataCopy(self) -> None:
        self.num_callDataCopy += 1

    def clear_num_callDataCopy(self) -> None:
        self.num_callDataCopy = 0

    def add_flag_keccak256(self) -> None:
        self.flag_keccak256 += 1

    def clear_flag_keccak256(self) -> None:
        self.flag_keccak256 = 0

    def add_num_keccak256(self) -> None:
        self.num_keccak256 += 1

    def clear_num_keccak256(self) -> None:
        self.num_keccak256 = 0

    def add_flag_getCallValue(self) -> None:
        self.flag_getCallValue += 1

    def clear_flag_getCallValue(self) -> None:
        self.flag_getCallValue = 0

    def add_num_getCallValue(self) -> None:
        self.num_getCallValue += 1

    def clear_num_getCallValue(self) -> None:
        self.num_getCallValue = 0

    def change_flag_getCallValue_in_function(self) -> None:
        self.flag_getCallValue_in_function = not self.flag_getCallValue_in_function

    def add_flag_revert(self) -> None:
        self.flag_revert = 1

    def clear_flag_revert(self) -> None:
        self.flag_revert = 0

    def add_flag_getCaller(self) -> None:
        self.flag_getCaller += 1

    def clear_flag_getCaller(self) -> None:
        self.flag_getCaller = 0

    def add_num_getCaller(self) -> None:
        self.num_getCaller += 1

    def clear_num_getCaller(self) -> None:
        self.num_getCaller = 0

    def add_flag_getCallDataSize(self) -> None:
        self.flag_getCallDataSize += 1

    def clear_flag_getCallDataSize(self) -> None:
        self.flag_getCallDataSize = 0
    
    def add_num_div(self) -> None:
        self.num_div += 1

    def clear_num_div(self) -> None:
        self.num_div = 0

    def add_num_mul(self) -> None:
        self.num_mul += 1

    def clear_num_mul(self) -> None:
        self.num_mul = 0

    def add_num_storageLoad(self) -> None:
        self.num_storageLoad += 1

    def clear_num_storageLoad(self) -> None:
        self.num_storageLoad = 0

    def add_flag_getExternalBalance(self) -> None:
        self.flag_getExternalBalance += 1

    def clear_flag_getExternalBalance(self) -> None:
        self.flag_getExternalBalance = 0

    def add_num_getExternalBalance(self) -> None:
        self.num_getExternalBalance += 1

    def clear_num_getExternalBalance(self) -> None:
        self.num_getExternalBalance = 0

    def add_flag_num_host(self) -> int:
        self.flag_num_host += 1
        return self.flag_num_host - 1

    def add_flag_num_wasm(self) -> int:
        self.flag_num_wasm += 1
        return self.flag_num_wasm - 1

    def add_dict_block_solver(self, key, value):
        if isinstance(value, z3.Solver):
            self.dict_block_solver[key] = list()
            self.dict_block_solver[key].append(value)
        elif utils.is_symbolic(value):
            self.dict_block_solver[key].append(value)
        elif isinstance(value, int):
            self.dict_block_solver[key].append(value)

    def add_dict_symbolic_address(self, key, value):
        self.dict_symbolic_address[key] = value

    def find_dict_root(self, key):
        dic = dict()
        if not (key in self.dict_symbolic_address):
            return 
        if isinstance(self.dict_symbolic_address[key], list):
            for item in self.dict_symbolic_address[key]:
                tmp = self.find_dict_root(item)
                if tmp:
                    dic.update(tmp)
            return dic
        else:
            dic[key] = self.dict_symbolic_address[key]
            return dic

    def clear_dict_symbolic_address(self):
        self.dict_symbolic_address.clear()

    def find_reentrancy_detection(self) -> None:
        self.ethereum_reentrancy_detection +=1
    
    def output_a_line(self,s:str):
        self.output_file.write(s+"\n")
    
    def output_before(self):
        self.output_file.write("""theory Contract
begin

functions: rep/2 [private], check_rep/2, get_rep/1
equations: check_rep(rep(m,loc),loc)=m, get_rep(rep(m,loc))=m

builtins: diffie-hellman,multiset

functions: true/0,false/0  

""")
    def output_after(self):
        self.output_file.write("""restriction single_init: // for a single init
        "All #i #j. Init0()@i & Init0()@j ==> #i=#j"
restriction single_transaction: // for a single transaction
    "All #i #j. Calleaction()@i & Calleaction()@j ==> #i=#j"

restriction predicate1:
"All #i a b. Pred_eq(a,b)@i ==> (a = b )"

restriction predicate2:
"All #i a b. Pred_not_eq(a,b)@i ==> not (a = b )"

lemma l1 :
//miss permission checke
"not (Ex #t1. SensitiveOp()@t1 & not (Ex #t2. Authenticate()@t2 & t2<t1))"
//"All #t1. SensitiveOp()@t1 ==> Ex #t2 .Authenticate()@t2 & t2<t1"

//lemma l2:
//exists-trace
//"Ex #t1. SensitiveOp()@t1"

lemma l3 :
//rollback
"not (Ex #t1 #t2. Send()@t1 & Block_State()@t2 & t2<t1)"

lemma l4 :
//overflow
"not (Ex #t1. OverFlow()@t1)"


lemma l5 :
//fake eos
"not (Ex #t1 #t2. Fake_EOS_Constraint()@t1 & On_Transfer()@t2 & t2<t1)"


lemma l6 :
//fake not
"not (Ex #t1 #t2. Fake_Notify_Constraint()@t1 & SensitiveOp()@t2 & t2<t1)"


lemma l7 :
//block info depend
"not (Ex #t1 #t2. Get_Block_State()@t1 & SensitiveOp()@t2 & t2<t1)"

end""")

global_vars = GlobalVariables()
