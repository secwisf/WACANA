from collections import defaultdict
import os,subprocess,time,json

from global_variables import global_vars
from argumentFactory import ABIObj, ArgumentFactory
from logAnalyzer import FeedbackFactory

def executeCommand(arguments, mustExecute = False):
    cmd = ' '.join(arguments)
    print("[-] executeCommand::", cmd)
    if mustExecute:
        testRound = 16
        while testRound > 0:
            testRound -= 1
            returnValue, out = subprocess.getstatusoutput(cmd)
            print("[-] executeCommand::", returnValue, out)
            if returnValue == 1 and "Expired Transaction" in out:
                continue
                
            elif returnValue in [0, 1]:
                return returnValue, out
        return False, ""

    else:
        r, o = subprocess.getstatusoutput(cmd)
        print(o)
        return r, o


def createAccount(name, publicKey, mustExecute = False):
    #executeCommand(global_vars.cleosExecutable + ' create account eosio ' + name + ' ' + publicKey, mustExecute)
    executeCommand([global_vars.cleosExecutable, 'create', 'account', 'eosio', name, publicKey], mustExecute)

def setContract(name, contractAddress, permission, mustExecute = False):
    #executeCommand(global_vars.cleosExecutable + ' set contract ' + name + ' ' + contractAddress, mustExecute)
    executeCommand([global_vars.cleosExecutable, 'set', 'contract', name, contractAddress, '-p', permission], mustExecute=mustExecute)

def pushAction(contract, action, arguments, permission, mustExecute = False):
    print(' '.join([global_vars.cleosExecutable, 'push', 'action', contract, action, '\'' + arguments + '\'', '-p', permission]))
    global_vars.logger.debug(' '.join([global_vars.cleosExecutable, 'push', 'action', contract, action, '\'' + arguments + '\'', '-p', permission])) #, '>> /dev/null 2>&1' if rpsRequired else ''
    return executeCommand([global_vars.cleosExecutable, 'push', 'action', 
     contract, action, '\'' + arguments + '\'', '-p', permission], mustExecute)#'--json' if rpsRequired else "--console"
     #, '' if rpsRequired else '>> /dev/null 2>&1'
    
def addCodePermission(name, mustExecute = False):
    #executeCommand(global_vars.cleosExecutable + ' set account permission ' + name + ' active --add-code', mustExecute)
    executeCommand([global_vars.cleosExecutable, 'set', 'account', 'permission', name, 'active', '--add-code'], mustExecute)

def getCurrency(account, permission, mustExecute = False):
    #executeCommand(global_vars.cleosExecutable + ' push action ' + contract + ' ' + action + ' \'' + arguments + '\' -p ' + permission + '@active', mustExecute)
    _, rt = executeCommand([global_vars.cleosExecutable, 'get', 'currency', 'balance', permission, account, 'EOS'], mustExecute)
    tmp = rt.split(' ')[0]
    return float(tmp) if tmp else 0

def getTable(account, scope,table, primary_key=None, binary=False,mustExecute = False):
    #executeCommand(global_vars.cleosExecutable + ' push action ' + contract + ' ' + action + ' \'' + arguments + '\' -p ' + permission + '@active', mustExecute)
    if primary_key:
        command=[global_vars.cleosExecutable, 'get', 'table', account, scope, table,'--lower',primary_key,'--limit','1']
    else:
        command=[global_vars.cleosExecutable, 'get', 'table', account, scope, table,'--limit','1']
    if binary:
        command.extend(['-b','1'])
    _, rt = executeCommand(command, mustExecute)
    return rt
    # tmp = rt.split(' ')[0]
    # return float(tmp) if tmp else 0



def initEosEnv():
    # init EOS environment & deploy contract
    os.system('killall -9 nodeos')
    os.system('killall -9 keosd')  

    os.system('rm -rf ' + global_vars.eosFilePath)
    os.system('rm ./nodeos.log')
    
    os.system("rm -rf ~/.local/share/eosio/nodeos/data/")
    os.system("rm -rf .local/share/eosio/ ~/eosio-wallet/")

    os.system('keosd --max-body-size 100000000 --unlock-timeout=3153600000 &')
    os.system("cleos wallet create -f ~/passwd")
    os.system('cat ~/passwd | cleos wallet unlock')
    os.system("cleos wallet import --private-key 5KQwrPbwdL6PhXujxW37FSSQZ1JiwsST4cqQzDeyXtP79zkvFD3")


    os.system(global_vars.nodeosExecutable + ' -e -p eosio\
                            --plugin eosio::chain_api_plugin \
                            --plugin eosio::http_plugin \
                            --plugin eosio::history_plugin \
                            --plugin eosio::history_api_plugin\
                            --access-control-allow-origin=\'*\' \
                            --contracts-console \
                            --http-validate-host=false \
                            --verbose-http-errors \
                            --max-transaction-time=1000 \
                            --max-body-size=102400000 \
                            --genesis-json genesis.json \
                            > nodeos.log 2>&1 &')
    time.sleep(2)
    # exit(0)
    

    # createAccount('clerk', global_vars.eosioTokenPublicKey, True)
    createAccount('eosio.token', global_vars.eosioTokenPublicKey, True)
    setContract('eosio.token', global_vars.eosioTokenContract, 'eosio.token@active', True)
    # print("set contract eosio.token")
    createAccount('bob', global_vars.eosioTokenPublicKey, True)
    addCodePermission('bob', True)

    pushAction('eosio.token', 'create', '["eosio","20000000000000.0000 EOS"]', 'eosio.token@active', True)
    pushAction('eosio.token', 'issue', '["eosio", "20000000000000.0000 EOS",""]', 'eosio@active', True)

    createAccount(global_vars.fakeTransferAgentName, global_vars.eosioTokenPublicKey, True)
    createAccount('fakeosio', global_vars.eosioTokenPublicKey, True)
    setContract(global_vars.fakeTransferAgentName, global_vars.eosioTokenContract, f'{global_vars.fakeTransferAgentName}@active', True)
    addCodePermission(global_vars.fakeTransferAgentName, True)
    addCodePermission('fakeosio', True)

    pushAction(global_vars.fakeTransferAgentName, 'create', '["fakeosio","200000000000000.0000 EOS"]', f'{global_vars.fakeTransferAgentName}@active', True)# fake EOS
    
    pushAction(global_vars.fakeTransferAgentName, 'issue', '["fakeosio", "20000000000000.0000 EOS",""]', 'fakeosio@active', True)
    
    pushAction('eosio.token', 'transfer', '["eosio","fakeosio","10000000.0000 EOS",""]', 'eosio@active', True)
    # pushAction('eosio.token', 'transfer', '["eosio","bob","1000.0000 EOS",""]', 'eosio@active', True)
    
    createAccount('testeosfrom', global_vars.eosioTokenPublicKey, True)
    addCodePermission('testeosfrom', True)
    pushAction('eosio.token', 'transfer', '["eosio","testeosfrom","10000000.0000 EOS",""]', 'eosio@active', True)

    pushAction('eosio.token', 'transfer', '["eosio","bob","1000.0000 EOS",""]', 'eosio@active', True)

    createAccount(global_vars.forgedNotificationTokenFromName, global_vars.eosioTokenPublicKey, True)
    pushAction('eosio.token', 'transfer', f'["eosio","{global_vars.forgedNotificationTokenFromName}","10000000.0000 EOS",""]', 'eosio@active', True)
    addCodePermission(global_vars.forgedNotificationTokenFromName, True)
    createAccount(global_vars.forgedNotificationAgentName, global_vars.eosioTokenPublicKey, True)
    setContract(global_vars.forgedNotificationAgentName, global_vars.atkforgContract, f'{global_vars.forgedNotificationAgentName}@active', True)
    pushAction(global_vars.forgedNotificationAgentName, 'regist', f'["{global_vars.contractName}"]', 'eosio@active', True)
    addCodePermission(global_vars.forgedNotificationAgentName, True)

    createAccount('atknoti', global_vars.eosioTokenPublicKey, True)
    setContract('atknoti', global_vars.atknotiContract, 'atknoti@active', True)
    addCodePermission('atknoti', True)

    # createAccount('atkrero', global_vars.eosioTokenPublicKey, True)
    # setContract('atkrero', global_vars.atkreroContract, 'atkrero@active', True)
    # addCodePermission('atkrero', True)

    # init contract
    pathContract =  global_vars.pathOfHookedContract + global_vars.contractName
    # os.system('eosio-cpp -o ' + global_vars.contractName+'.wasm' + ' ' + pathContract+'.cpp' + ' -DCONTRACT_NAME=\\"' + global_vars.contractName + '\\"')

    createAccount(global_vars.contractName, global_vars.aPublicKey)
    pushAction('eosio.token', 'transfer', f'["eosio","{global_vars.contractName}","1000.0000 EOS",""]', 'eosio@active', True)
    addCodePermission(global_vars.contractName)
    setContract(global_vars.contractName, pathContract, global_vars.contractName+'@active')
    # addCodePermission(global_vars.fakeTransferAgentName, True)
    

def get_action_info(path_of_abi,path_of_wasm):
    contract_name=global_vars.contractName
    contractABI,feedbackFactory=instrument(path_of_abi,path_of_wasm)
    initEosEnv() 
    testDataFactory=ArgumentFactory(contractABI,contract_name)
    os.system(f"rm -f {global_vars.logPath}/*")
    # print(testDataFactory.functionName)
    action_name_to_function_id={}
    action_name_to_test_args={}
    store_logs=[]
    global_vars.log_count=len(contractABI.actionNames)
    for i,action_name in enumerate(contractABI.actionNames):
        if action_name=='transfer':
            testDataFactory.generateNewData(action_name,4)
            testDataFactory.generateNewDataType(action_name)
            pushAction('eosio.token', 'transfer', testDataFactory.testArgument, 'bob@active', True)
            # pushAction(contract_name,action_name,f"{testDataFactory.testArgument}",contract_name+"@active",True)
        testDataFactory.generateNewData(action_name,0)
        # print(testDataFactory.testArgument)
        testDataFactory.generateNewDataType(action_name)
        # print(testDataFactory.testArgument)
        # pushAction(testDataFactory.executedContractName,action_name,f"{testDataFactory.testArgument}",testDataFactory.executedContractName+"@active",True)
        pushAction(contract_name,action_name,f"{testDataFactory.testArgument}",contract_name+"@active",True)
        # pushAction(contract_name,action_name,f"{testDataFactory.testArgument}","bob@active",True)
        global_vars.plogPath=global_vars.pathOfHookedContract+f"/log{i}.txt"
        xfunid,n_store_logs=feedbackFactory.processLog(f_type=testDataFactory.testArgumentType)
        if all([x==-1 for x,v in xfunid]):
            continue
        store_logs.extend(n_store_logs)
        # print(feedbackFactory.firstActEntry)#action function id
        for x,l in xfunid:
            if x!=-1 and x not in action_name_to_function_id.values() and l==len(testDataFactory.testArgumentType)+1:
                action_name_to_function_id[action_name]=x
                break
        action_name_to_test_args[action_name]=(testDataFactory.testArgument,testDataFactory.testArgumentType,[i['name'] for i in testDataFactory.getStructDetail(testDataFactory.getActionType(action_name))['fields']])#字符串形式的测试数据，测试数据的类型数组，测试数据的字段名
    return action_name_to_function_id,action_name_to_test_args,store_logs,feedbackFactory

# @profile
def exec_on_chain(feedbackFactory,action_name,test_argument_str,test_argument_type):
    contract_name=global_vars.contractName
    # if action_name=='transfer':
    #     pushAction('eosio.token', 'transfer', test_argument_str, 'bob@active', True)
    # else:
    if action_name=='transfer':
        test_argument=json.loads(test_argument_str)
        if test_argument["from"]!=contract_name:
            test_argument["from"]='bob'
            test_argument_str=json.dumps(test_argument)
        pushAction('eosio.token', 'transfer', test_argument_str, test_argument['from']+'@active', True)
        # pushAction(contract_name,action_name,f"{testDataFactory.testArgument}",contract_name+"@active",True)
    else:
        # print(testDataFactory.testArgument)
        # pushAction(testDataFactory.executedContractName,action_name,f"{testDataFactory.testArgument}",testDataFactory.executedContractName+"@active",True)
        pushAction(contract_name,action_name,test_argument_str,"bob@active",True)
        global_vars.plogPath=global_vars.pathOfHookedContract+f"/log{global_vars.log_count}.txt"
        global_vars.log_count+=1
        i,store_logs=feedbackFactory.processLog(f_type=test_argument_type)
        global_vars.storage.add_logs(store_logs)
        pushAction(contract_name,action_name,test_argument_str,contract_name+"@active",True)
    global_vars.plogPath=global_vars.pathOfHookedContract+f"/log{global_vars.log_count}.txt"
    global_vars.log_count+=1
    print("processLog")
    i,store_logs=feedbackFactory.processLog(f_type=test_argument_type)
    global_vars.storage.add_logs(store_logs)

def clear_env():
    # os.system("rm -rf ~/.local/share/eosio/nodeos/data/")
    # time.sleep(2)
    os.system(f"rm -f {global_vars.logPath}/*")
    initEosEnv()


def test():
    global_vars.contractName="addressbook"
    # global_vars.contractName="pet"
    # global_vars.contractName="hello"
    contractName = global_vars.contractName
    # contractABI,feedbackFactory=instrument("./examples/EOSIO_contracts/hello/hello.abi","./examples/EOSIO_contracts/hello/hello.wasm")
    # global_vars.contractName="hello"
    # contractABI,feedbackFactory=instrument(f"./examples/EOSIO_contracts/{contractName}/{contractName}.abi",f"./examples/EOSIO_contracts/{contractName}/{contractName}.wasm")
    contractABI,feedbackFactory=instrument(f"./{contractName}/{contractName}.abi",f"./{contractName}/{contractName}.wasm")
    initEosEnv() 
    testDataFactory=ArgumentFactory(contractABI,contractName)
    os.system(f"rm -f {global_vars.logPath}/*")
    # print(testDataFactory.functionName)
    action_name_to_function_id={}
    action_name_to_test_args={}
    for i,action_name in enumerate(contractABI.actionNames):
        # print(action_name)
        testDataFactory.generateNewData(action_name,0)
        # print(testDataFactory.testArgument)
        testDataFactory.generateNewDataType(action_name)
        # print(testDataFactory.testArgument)
        pushAction(testDataFactory.executedContractName,action_name,f"{testDataFactory.testArgument}",testDataFactory.executedContractName+"@active",True)
        global_vars.plogPath=global_vars.pathOfHookedContract+f"/log{i}.txt"
        feedbackFactory.processLog()
        # print(feedbackFactory.firstActEntry)#action function id
        action_name_to_function_id[action_name]=feedbackFactory.firstActEntry
        action_name_to_test_args[action_name]=list(zip(testDataFactory.testArgument,testDataFactory.testArgumentType))
    print(action_name_to_function_id)
    print(action_name_to_test_args)

        # os.system(f"rm -f {global_vars.logPath}/*")


def instrument(pathABI,pathWasm):
    contractName=global_vars.contractName
    os.system(f"rm .tmpRes.txt")

    # init ./rt_info
    rtContractDir = f'{global_vars.pathOfHookedContract}/{contractName}/'
    print("rtContractDir",rtContractDir )
    os.system(f'rm -rf {global_vars.pathOfHookedContract} ; mkdir {rtContractDir} -p')
    
    # modify .abi
    with open(pathABI,'r') as f:
        normalABI = json.load(f)
    # print(pathABI)
    if 'version' not in normalABI or normalABI['version']=='':
        normalABI['version']="eosio::abi/1.0"
    # print(normalABI)
    if 'transfer' not in [item['name'] for item in normalABI['actions']]:
        normalABI['actions'].append(        
            {"name":"transfer","type":"transfer","ricardian_contract":""}
        )
        normalABI['structs'].append(
            {"name":"transfer","base":"","fields":[{"name":"from","type":"name"},{"name":"to","type":"name"},{"name":"quantity","type":"asset"},{"name":"memo","type":"string"}]}
        )
    # new abi
    with open(f'{rtContractDir}/{contractName}.abi', 'w') as f:
        json.dump(normalABI, f)

    # .wasm instrumentation
    os.system(f'cp {pathWasm} {global_vars.pathOfHookedContract}') # original wasm

    # wasabi
    os.system(f'wasabi {pathWasm} {global_vars.pathOfHookedContract}')
    os.system(f"mv ./{pathWasm.split('/')[-1].split('.wasm')[0]}.txt {global_vars.pathOfHookedContract}/{contractName}.txt")
    os.system(f'mv {global_vars.pathOfHookedContract}/{contractName}.wasm {rtContractDir}/{contractName}.wasm')
    # os.system(f'rm -rf ./out')

    # for analysis
    os.system(f"mkdir {global_vars.pathOfHookedContract}/rLogs/") #       raw logs
    os.system(f"mkdir {global_vars.pathOfHookedContract}/pLogs/") # processed logs
    
    return ABIObj(f'{rtContractDir}/{contractName}.abi'), FeedbackFactory()


# def fuzz(contractABI, feedbackFactory, in_atk=()):
#     contractName = global_vars.contractName
#     # tmpLogger = utils.Logger(os.getenv('HOME') + '/dynamicAnalyze/EOSFuzzer/symzzer/.tmpRes.txt')

#     global idxPeriod
#     logging.info(f"{'='*20} {contractName} {'='*20}")

#     testDataFactory = ArgumentFactory(contractABI, contractName)

#     # init eosio platform
#     initEosEnv() 

#     # locate eosponser 我们只分析涉及到 eos 的合约
#     os.system(f'rm -r {global_vars.logPath}* ; rm {global_vars.plogPath}')
#     pushAction('eosio.token', 'transfer', '[ "testeosfrom", "' + global_vars.contractName + '","100.0000 EOS","FUZZER"]', 'testeosfrom@active', mustExecute=True)
    
#     # try:
#     feedbackFactory.getTransferEntry() # target eosponser
#     with open(f"{global_vars.pathOfHookedContract}/actPartly.txt", 'w') as f:
#         f.write( str(feedbackFactory.applyFuncId) + " " + str(feedbackFactory.transferEntry))

#     # return False

#     acceptEOSToken = False
#     isFixForgedBug = False
#     rejectFakeos = list()
#     pmSafeActs = list()

#     # fuzzing
#     candidateKinds = [0, 1, 2, 3, 4]# [0, 0, 0, 0, 0, 1, 1, 2, 2, 1, 2, 3, 4]
#     '''
#     0: invoke one action of S
#     1: fake notification payload
#     2: fake EOS payload.1
#     3: fake EOS payload.2
#     4: transfer valid EOS
#     '''
#     idxPeriod = 0
#     kind = 0

#     while idxPeriod <= global_vars.maxPeriod:
#         print("[+] round = ", idxPeriod)
#         idxPeriod += 1

#         if isFixForgedBug and 1 in candidateKinds:
#             candidateKinds.remove(1)
#         if acceptEOSToken and 2 in candidateKinds:
#             candidateKinds.remove(2)
#             candidateKinds.remove(3)
#         if kind != 0:
#             kind = 0
#         else:
#             kind = random.choice(candidateKinds)

#         # kind = 3 if idxPeriod == 1 else candidateKinds[idxPeriod%len(candidateKinds)]
#         # kind = 2 if idxPeriod == 2 else candidateKinds[idxPeriod%len(candidateKinds)]
#         # kind = 1 if idxPeriod == 3 else candidateKinds[idxPeriod%len(candidateKinds)]

#         if global_vars.isChkOOB == FFMODE:
#             kind = random.choice([0, 4])

#         elif global_vars.isFakeEos == FFMODE:
#             kind = random.choice([2, 3])


#         elif global_vars.isFakeNot == FFMODE:
#             kind = random.choice([0, 1, 4])

#         # kind = 4 
#         print('[-] kind = ', kind)
#         # 1. choose function
#         _fc = ":ALL"
        
#         # 考虑把以下代码放入 argumentFactory.py
#         lofter = random.choice([0,1])
#         if kind == 0 and lofter:
#             prexFc =  testDataFactory.functionName
#             if prexFc in feedbackFactory.rdb:
#                 rdbs = feedbackFactory.rdb[testDataFactory.functionName] # table
#                 if rdbs != []:
#                     fs = []
#                     for rdb in rdbs:
#                         if rdb in feedbackFactory.dbFlow:
#                             fs.extend(feedbackFactory.dbFlow[rdb]['w'])
#                     if fs != []:
#                         _fc = random.choice(fs)
        
#         # kind = 0
#         # _fc = "test"
#         # =======================================

#         # 2. generate cleos command
#         testDataFactory.generateNewData(_fc, kind)
#         currentFuncName = testDataFactory.functionName
#         global_vars.logger.info(f'================= testing {currentFuncName} ==========================')
#         testDataFactory.generateNewDataType(currentFuncName)
        
#         fbSeed = feedbackFactory.seeds(kind, currentFuncName)

#         # if fbSeed == []:
#         #     testArgumentStr = testDataFactory.testArgument
#         #     feedbackFactory.seedDict[(kind, currentFuncName)].append(newSeed)

#         # else:
#         #     testArgumentStr = json.dumps(fbSeed) 

        
#         testArgumentStr = json.dumps(fbSeed) if fbSeed != [] else testDataFactory.testArgument

#         # 3. execute cleos

#         os.system(f"rm {global_vars.logPath}/* ; rm {global_vars.plogPath}")

#         cmd = ' '.join(['cleos', 'push', 'action', testDataFactory.executedContractName,
#                  currentFuncName, '\'' + testArgumentStr + '\'', '-p', f'{testDataFactory.activeAccount}@active'])
        
#         global_vars.logger.info(cmd)  
#         # cmd = in_cmd
#         feedbackFactory.cmds.append(cmd)

#         PriBalance = getCurrency(global_vars.contractName, 'eosio.token')
#         atkPriBalance = getCurrency("testeosfrom", 'eosio.token')
#         print('[+] Execute Cleos CMD: ', cmd)
#         returnValue, out = subprocess.getstatusoutput(cmd) # sync with nodeos 太慢了？？？
#         AftBalance = getCurrency(global_vars.contractName, 'eosio.token')
#         atkAftBalance = getCurrency("testeosfrom", 'eosio.token')
#         print('[+] target currency: ', PriBalance, AftBalance)
#         print('[+] atker currency: ', atkPriBalance, atkAftBalance)
#         if atkPriBalance < atkAftBalance:
#             # print("YEEEEEEEEEEEEEEEEEEEEEH", global_vars.contractName)
#             with open ("/home/szh/dynamicAnalyze/EOSFuzzer/symzzer/.exploits", "w+") as f:
#                 f.write(f"{global_vars.contractName}   {cmd}\n")

#         print(returnValue, out)
        
#         if os.listdir(global_vars.logPath):
#             global_vars.timePoints.append((int(sorted(os.listdir(global_vars.logPath), key=lambda fname: int(fname[4:-4]))[0][4:-4]), time.time()))
#         # print('[----------] executed cmd:', out, '@@@')
#         # print('\n'*5)

#         os.system(f'cp {global_vars.logPath}/* {global_vars.pathOfHookedContract}/rLogs/') # for coverage
            
#         # print('_____++++++++++++++====end', subprocess.getstatusoutput(f'ls {global_vars.logPath}'))
#         isExecuted = True if returnValue == 0 else False
#         if 'ABI has an unsupported version' in out:
#             return False
#         if 'Duplicate transaction' in out or 'Expired Transaction' in out:
#             continue

#         # 4. deserialize logs
#         if not feedbackFactory.processLog('Error' not in out):
#             if kind in (2,3):
#                 if kind not in rejectFakeos:
#                     rejectFakeos.append(kind)
#                 if len(rejectFakeos) == 2 and global_vars.isFakeEos == FFMODE:
#                     return True
#             if kind == 1 and global_vars.isFakeNot == FFMODE:
#                 return True
#             continue

#         if global_vars.isChkOOB != DISABLE and kind == 0 and 'out of bounds memory access' in out:
#             global_vars.bugSet.append(3)
#             return True
#             # print(feedbackFactory.firstActLog[-1])
#             atkFID, atkOffset, atkClen = in_atk
#             # print(feedbackFactory.firstActLog[-1], '============', atkFID)
#             func, offset = feedbackFactory.firstActLog[-1][2][:2]
#             if func != atkFID:
#                 continue
#             elif func == atkFID and offset == atkOffset + atkClen - 1:# crach with OUT OF BRAND
#                 return True

#         # extract info from logs

#         print("+++++++++++++++++++++++++++++++++++++++++++++++++==")
#         try:
#             feedbackFactory.locateActionPos(index=0, txFuncName=currentFuncName)  # also collect information for first action
#         except :
#             print("[-] fuzzActions:: ERROR when location actions\n")
#             continue

#         # save processed logs
#         logTuple = [feedbackFactory.firstActLog, feedbackFactory.firstActPos] # logs, line_pos
#         with open(f"{global_vars.pathOfHookedContract}/pLogs/{idxPeriod}_{kind}.json", 'w') as f:
#             json.dump([logTuple, testDataFactory.testArgumentType, json.loads(testArgumentStr), cmd], f)

#         if global_vars.detectVul:
#             # the detectors
#             try:
#                 if global_vars.isChkPems != DISABLE and 6 not in global_vars.bugSet:
#                     if feedbackFactory.authCheckFault():
#                         logging.info("permission check fault")
#                         global_vars.bugSet.append(6)

#                         # fast mode
#                         if global_vars.isChkPems == FFMODE:
#                             return True
#                     # else:
#                     #     pmSafeActs.append(currentFuncName)
#                     #     if len(pmSafeActs) == len(testDataFactory.abi.actionNames):
#                     #         return False

#                 if global_vars.isBlockinfoDep != DISABLE and 7 not in global_vars.bugSet:
#                     if feedbackFactory.usedTaposFunctionThenEosioTokenTransfer():
#                         # success
#                         logging.info("Tapos Warning")
#                         global_vars.bugSet.append(7)
                        
#                         # fast mode
#                         if global_vars.isBlockinfoDep == FFMODE:
#                             return True
                        
#                         if (global_vars.isBlockinfoDep, global_vars.isRollback) == (ENABLE, ENABLE) \
#                                 and (7 in global_vars.bugSet and 8 in global_vars.bugSet):
#                             return True

#                 if global_vars.isRollback != DISABLE and 8 not in global_vars.bugSet:
#                     if feedbackFactory.rollback():
#                         # success
#                         logging.info("rollback Warning")
#                         global_vars.bugSet.append(8)

#                         # fast mode
#                         if global_vars.isRollback == FFMODE:
#                             return True

#                         if (global_vars.isBlockinfoDep, global_vars.isRollback) == (ENABLE, ENABLE) \
#                                 and (7 in global_vars.bugSet and 8 in global_vars.bugSet):
#                             return True

#                 if global_vars.isFakeNot != DISABLE and isFixForgedBug == False and kind == 1:
#                     '''
#                     if idxPeriod > 100:
#                         # did't find a protection 
#                         global_vars.logger.info("Fake Notification: did't touch protection")
#                         global_vars.bugSet.append(1)

#                         if global_vars.isFakeNot == FFMODE:
#                             return True
#                     '''
                    
#                     _magic = feedbackFactory.checkForgedNotificationBug(testDataFactory.forgedNotificationAgentName, contractName, isExecuted)
#                     # print('[-] fake notification detector begins~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~', _magic)
#                     if _magic == 0:
#                         isFixForgedBug = True
#                         global_vars.bugSet.append(-11)
#                         if global_vars.isFakeNot == FFMODE:
#                             return True
                
#                     elif _magic == 1: 
#                         global_vars.logger.info("Fake Notification")
#                         if 1 not in global_vars.bugSet:
#                             global_vars.bugSet.append(1)
                        

#                 if global_vars.isFakeEos != DISABLE and kind in [2, 3] and 2 not in global_vars.bugSet:
#                     print("-----------------------------testing fake eos ---------------")
#                     if feedbackFactory.hasFakeTransferBug(testDataFactory.executedContractName):
#                         global_vars.logger.info(f"Has fake transfer bug;Fake EOS kind={kind}")
#                         global_vars.bugSet.append(2)

#                     if global_vars.isFakeEos == FFMODE:
#                         return True
            

#                 # elif global_vars.isFakeEos != DISABLE and kind == 2 and 2 not in global_vars.bugSet:
#                 #     if feedbackFactory.hasFakeTransferBug():
#                 #         global_vars.logger.info(f"Has fake transfer bug;Fake EOS kind={kind}")
#                 #         global_vars.bugSet.append(2)
#                 #         if global_vars.isFakeEos == FFMODE:
#                 #             return True

#                 # elif global_vars.isFakeEos != DISABLE and kind == 3 and 3 not in global_vars.bugSet:
#                 #     acceptEOSToken = feedbackFactory.hasFakeTransferBug()
#                 #     if acceptEOSToken:
#                 #         global_vars.logger.info(f"Has fake transfer bug;Fake EOS kind={kind}")
#                 #         global_vars.bugSet.append(3)
#                 #         if global_vars.isFakeEos == FFMODE:
#                 #             return True
#             except:
#                 print('[-] Scanner Error')
#         # if kind == 1:
#         #     exit(0)

            
#         if True and (kind == 0 or (kind in (1, 4) and feedbackFactory.transferEntry == feedbackFactory.caseInfo[2])):
#             '''
#             inactive feeback when detecting Fake EOS, as it is unnecessary to analyze action function.
#             '''
#             # 5. feedback base on symbolic execution
#             print('-------------------- emulator -------------------', idxPeriod)
#             if global_vars.globalDebug:
#                 print("??? test argument=", testArgumentStr)
#                 print("??? test argument types =", testDataFactory.testArgumentType)

#             cleosJson = json.loads(testArgumentStr)
#             inputType = testDataFactory.testArgumentType

#             wasabi = Wasabi(inputType, cleosJson, feedbackFactory.importsFunc, feedbackFactory.firstActEntry)
            
#             # handling first action
#             startPos, endPos, _, _ = feedbackFactory.caseInfo
#             actionLog = feedbackFactory.firstActLog[startPos-1:endPos]
#             # print("[-] fuzzActions.wasabiInput::", actionLog)
#             for line in actionLog:
#                 try:
#                     # if wasabi.analysis.timeoutCnt >= 4:
#                     #     break
#                     _, instr, args, types = line
#                     # print("--debug:logAll:--", instr, args, types,"STACK",wasabi.analysis.stack.peek(), cmd)
#                     # print('-actFuzzer: args=',args)
#                     symArgs = taintutils.buildArgs(instr, args, types)
#                     # print('-actFuzzer: symArgs=',symArgs)
#                     # print("[-] wasabi hook-begin")
#                     wasabi.lowlevelHooks(instr, symArgs)
#                     # print("[-] wasabi hook-end")

#                 except Exception as e:
#                     print('[-] EOSVM Model ERROR:', e)
#                     break # drop

#             # exit()
#             threadPool = list()
#             for _, constraint in wasabi.analysis.queue:
#                 i_context = z3.Context()
#                 i_constraint = copy.deepcopy(constraint).translate(i_context)
#                 thread = utils.myThread(i_constraint, i_context)
#                 thread.start()
#                 threadPool.append(thread)
                
#             # exit()   
#             z3Models = list()
#             for thread in threadPool:  
#                 thread.join()  
#                 z3Models.append(thread.get_result())
                     
#             for cfb, z3Model in zip([cfb for cfb, _ in wasabi.analysis.queue], z3Models):
#                 if z3Model == [None]:
#                     continue
#                 try:
#                     wasabi.analysis.seedMining(cfb, z3Model)
#                 except:
#                     pass
#                     # abi mismatch
            

#             print("[+] =========== output new seeds ====================")
#             print(wasabi.analysis.cleosArgs)
#             # exit()
#             newSeeds = list()
#             f = lambda data, k : list(data.keys())[k] 
#             for location, argPosTuple, value in wasabi.analysis.cleosArgs:
#                 # TODO 将此 touched branches filter 转移至analysis.solve()中

#                 if location in feedbackFactory.touchedBrs[(kind, currentFuncName)]:
#                     continue

#                 # print('[+] New Seed Tuple:', argPos, value, seeds)
#                 seed = cleosJson.copy()
#                 layout_o, layout_i = argPosTuple

#                 key = f(cleosJson, layout_o)
#                 if layout_i != -1:
#                     # struct
#                     if global_vars.globalDebug:
#                         print(seed, key, layout_i, '@@')
#                     ikey = f(seed[key], layout_i)
#                     seed[key][ikey] = value
#                     if global_vars.globalDebug:
#                         print(f"cmd={cmd} ---- newSeed={seed}, argPosTuple={argPosTuple}, value={value}")

#                 else:
#                     seed[key] = value 

#                 newSeed = (location, seed)
#                 feedbackFactory.seedDict[(kind, currentFuncName)].append(newSeed)
#                 feedbackFactory.touchedBrs[(kind, currentFuncName)].add(location)
#                 # print(json.dumps(seed))
#                 # print(feedbackFactory.seedDict[currentFuncName])
#                 # exit()
#                 print('[+] newSeed generated:', newSeed)
        
#             print('[+++++++++++] ============ runtime debug ================')
#             for cmd in feedbackFactory.seedDict[(kind, currentFuncName)]:
#                 print("[+] seed Pools:", cmd, '\n')
#             # exit()
     
#     return True
if __name__ == "__main__":
    test()
