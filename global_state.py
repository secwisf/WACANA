from copy import copy, deepcopy
class GlobalState:
    def __init__(self,
                 wstate=None,
                 constraints=None,
                 pc_traces=None,
                 func_id=None,
                 storage=None,
                 write_storage=None,
                 # transactions=None
                 ):
        self.wstate = wstate
        self.constraints = constraints if constraints is not None else []
        self.pc_traces = pc_traces if pc_traces is not None else []#用于统计覆盖率
        self.func_id = func_id if func_id is not None else -1
        self.storage = storage if storage is not None else None
        # self.write_storage = write_storage if write_storage is not None else False
        # self.transactions = transactions if transactions is not None else []#放已经产生的交易(函数名，参数)

    def __copy__(self):
        
        return GlobalState(
            copy(self.wstate),
            copy(self.constraints),
            copy(self.pc_traces),
            copy(self.func_id),
            copy(self.storage)
        )

    def __str__(self):
        # return f'GlobalState: {id(self)}'
        return str(self.pc_traces)

    def __repr__(self):
        return self.__str__()
    
    def add_pc(self, pc):
        self.pc_traces.append(pc)

    def add_constraint(self, cons):
        self.constraints.append(cons)

    def delete_constraint(self):
        self.constraints.pop()

    def is_empty(self):
        return len(self.pc_traces)==0 and len(self.constraints)==0

    def __add__(self, other):
        return GlobalState(self.wstate,self.constraints+other.constraints,self.pc_traces+other.pc_traces)
        # return GlobalState(self.wstate,self.constraints+other.constraints,self.pc_traces+other.pc_traces,self.storage+other.storage)
