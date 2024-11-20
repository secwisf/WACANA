#!/usr/bin/python3
# -*- coding: utf-8 -*-

from fuzz import getTable
from utils import eos_int_to_abi, gen_symbolic_args, gen_symbolic_value, is_bv_concrete, get_concrete_int
import json
from z3 import If, is_bv, BitVecVal
from random import randint
import bin_format

class Storage():
    def __init__(self, store_logs):
        self.store_logs=[]
        self.keys=[]
        self.iters=[]
        self.add_logs(store_logs)
        self.eos_table=[]
        # self.store_logs = store_logs
        # self.keys=self.get_primary_keys(store_logs)

    def get_primary_keys(self, store_logs):
        res=[]
        for log in store_logs:
            res.append((int(log[2][10])<<32)+int(log[2][9]))
        return res

    def get_iters(self, store_logs):
        res=[]
        for log in store_logs:
            res.append(int(log[2][-1]))
        return res       

    # @profile
    def add_logs(self, store_logs):
        print("new logs:",store_logs)
        for log in store_logs:
            if log[1]=='store' and (int(log[2][10])<<32)+int(log[2][9]) not in self.keys:
                self.store_logs.append(log)
            elif log[1]=='remove':
                for i in range(len(self.store_logs)-1,-1,-1):
                    
                    if self.store_logs[i][2][-1]==log[2][-1]:
                        del self.store_logs[i]
            else:
                print(log)
        self.keys=self.get_primary_keys(self.store_logs)
        self.iters=self.get_iters(self.store_logs)

    def find(self,code,scope,table,id):
        if is_bv_concrete(code) and eos_int_to_abi(code)=="eosio.token":
            self.eos_table.append((eos_int_to_abi(scope),eos_int_to_abi(table)))
            return gen_symbolic_value(bin_format.i32,f"eos_iter{len(self.eos_table)-1}")
        if is_bv_concrete(id):
            # print("code",eos_int_to_abi(code))
            # print("scope",eos_int_to_abi(scope))
            # print("table",eos_int_to_abi(table))
            id=get_concrete_int(id)
            if id in self.keys:
                return self.iters[self.keys.index(id)]
            else:
                return -1
        else:
            if len(self.keys)==0:
                return -1
            # return -1
            res=BitVecVal(-1,32)
            print("begin construct if table")
            print("len of keys",len(self.keys))
            i=randint(0,len(self.keys))
            for i,k in enumerate(self.keys):
                res=If(id==k,BitVecVal(int(self.iters[i]),32),res)
            print(res)
            return res


    def get_key_by_iter(self, iter):
        return self.keys[self.iters.index(iter)]

    def store(self,scope,table,payer,id,data,len):
        pass
        # lower_mask=0xffffffff
        # higher_mask=0xffffffff00000000
        # self.store_logs.append([0, 'call offline', [142, 161, 33, scope&lower_mask, scope&higher_mask, table&lower_mask, table&higher_mask, payer&lower_mask, payer&higher_mask, id&lower_mask, id&higher_mask, data, len], ['I64', 'I64', 'I64', 'I64 ', 'I32', 'I32']])
        # self.keys.append(id)
        
    def get_bin(self,contract_name,iterator,states):
        if is_bv_concrete(iterator):
            iterator=get_concrete_int(iterator)
            # print("scope",eos_int_to_abi(scope))
            # print("table",eos_int_to_abi(table))
            index=self.iters.index(iterator)
            scope=(self.store_logs[index][2][4]<<32)+self.store_logs[index][2][3]
            table=(self.store_logs[index][2][6]<<32)+self.store_logs[index][2][5]
            payer=(self.store_logs[index][2][8]<<32)+self.store_logs[index][2][7]
            print(f"scope:{scope},{eos_int_to_abi(scope)},table:{table},{eos_int_to_abi(table)}")
            # if eos_int_to_abi(code)=="eosio.token":
                # return 1
            if iterator not in self.iters:
                return None
            try:
                res= json.loads(getTable(contract_name,eos_int_to_abi(scope),eos_int_to_abi(table),str(self.keys[index]),True))['rows'][0]
            except:
                res=""
            print(res,type(res))
            return res
        else:
            if "eos_iter" in str(iterator):
                i=int(str(iterator)[8:])
                try:
                    res= json.loads(getTable("eosio.token",self.eos_table[i][0],self.eos_table[i][1],None,binary=True))['rows'][0]
                except:
                    res=""
                print(res,type(res))
                return res
            for s in states:
                s.add_constraint(iterator==self.iters[0])
            return self.get_bin(contract_name,int(self.iters[0]),states)
            

    # def __add__(self, other):
    #     old_key=self.keys
    #     all_log=self.store_logs
    #     for i,k in enumerate(other.keys):
    #         if k in old_key:
    #             iter=old_key.index(k)
    #             all_log[iter]=other.store_logs[i]
    #         else:
    #             all_log.append(other.store_logs[i])
    #     return Storage(all_log)

    def __len__(self):
        return len(self.store_logs)
    
    # def resize(self,old_len):
    #     if old_len>len(self.store_logs):
    #         return False
    #     self.store_logs=self.store_logs[:old_len]
    #     self.keys=self.keys[:old_len]
    #     return True

    def lowerbound(self,code,scope,table,id,states):
        if len(self.store_logs)==0:
            return -1
        if is_bv_concrete(id):
            id=get_concrete_int(id)
            mini=-1
            for i,k in enumerate(self.keys):
                if k>=id and (mini<0 or k<self.keys[mini]):
                    mini=i
            return self.iters[mini] if mini>=0 else self.iters[len(self.store_logs)-1]
        else:
            for s in states:
                s.add_constraint(id==self.keys[-1])
            return self.end(code,scope,table)

    def upperbound(self,code,scope,table,id,states):
        if len(self.store_logs)==0:
            return -1
        if is_bv_concrete(id):
            id=get_concrete_int(id)
            mini=-1
            for i,k in enumerate(self.keys):
                if k>id and (mini<0 or k<self.keys[mini]):
                    mini=i
            return self.iters[mini] if mini>=0 else self.iters[len(self.store_logs)-1]
        else:
            for s in states:
                s.add_constraint(id==self.keys[-1])
            return self.end(code,scope,table)

    def end(self,code,scope,table):
        return self.iters[len(self.store_logs)-1]
