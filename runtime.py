# !/usr/bin/python3
# -*- coding: utf-8 -*-
"""
The module includes components of module instance, these instances will be
constructed only when WebAssembly module is instantiated.
"""

import typing
import bin_format
import structure
import z3
import utils
import copy


class Store:
    """The store represents all global state that can be manipulated by WebAssembly programs. It consists of the runtime
    representation of all instances of functions, tables, memories, and globals that have been allocated during the
    life time of the abstract machine
    Syntactically, the store is defined as a record listing the existing instances of each category:
    store ::= {
        funcs funcinst∗
        tables tableinst∗
        mems meminst∗
        globals globalinst∗
    }

    Addresses are dynamic, globally unique references to runtime objects, in contrast to indices, which are static,
    module-local references to their original definitions. A memory address memaddr denotes the abstract address of
    a memory instance in the store, not an offset inside a memory instance.

    Attributes:
        funcs: list of function instance
        tables: list of table instance
        mems: list of memory instance
        globals: list of global instance
    """

    def __init__(self):
        self.funcs: typing.List[FunctionInstance] = []
        self.tables: typing.List[TableInstance] = []
        self.mems: typing.List[MemoryInstance] = []
        self.smems: typing.List[SymbolicMemoryInstance] = []#symbolic memorys
        self.globals: typing.List[GlobalInstance] = []
        self.visited = []


class FunctionInstance:
    """A function instance is the runtime representation of a function. It effectively is a closure of the original
    function over the runtime module instance of its originating module. The module instance is used to resolve
    references to other definitions during execution of the function.

    funcinst ::= {type functype,module moduleinst,code func}
               | {type functype,hostcode hostfunc}
    hostfunc ::= ...
    """

    def __init__(self):
        pass


class WasmFunc(FunctionInstance):
    """A wasm function is a function expressed by WebAssembly bytecode, which may be called in current module or
    another module.

    Attributes:
        functype: represent the wasm function type
        module: the module include wasm function itself
        code: the instructions of wasm function
    """

    def __init__(self, functype: structure.FunctionType, module: 'ModuleInstance', code: structure.Function):
        super().__init__()
        self.functype = functype
        self.module = module
        self.code = code


class HostFunc(FunctionInstance):
    """A host function(库函数) is a function expressed outside WebAssembly but passed to a module as an import. The definition
    and behavior of host functions are outside the scope of this specification. For the purpose of this
    specification, it is assumed that when invoked, a host function behaves non-deterministically, but within certain
    constraints that ensure the integrity of the runtime.

    Attributes:
        functype: represent the wasm function type
        hostcode: the native code reference
    """

    def __init__(self, functype: structure.FunctionType, hostcode: typing.Callable, funcname: str):
        super().__init__()
        self.functype = functype
        self.hostcode = hostcode
        self.funcname = funcname


class TableInstance:
    """A table instance is the runtime representation of a table. It holds a vector of function elements and an optional
    maximum size, if one was specified in the table type at the table’s definition site.
    Each function element is either empty, representing an uninitialized table entry, or a function address. Function
    elements can be mutated through the execution of an element segment or by external means provided by the embedder.

    tableinst ::= {elem vec(funcelem), max u32?}
    funcelem ::= funcaddr?

    It is an invariant of the semantics that the length of the element vector never exceeds the maximum size, if
    present.

    Attributes:
        elemtype: represent the type of elements in table
        limits: Limit instance represnt the size of table
        elem: the elements of table
    """

    def __init__(self, elemtype: int, limits: structure.Limits):
        self.elemtype = elemtype
        self.limits = limits
        self.elem = [None for _ in range(limits.minimum)]


class MemoryInstance:
    """A memory instance is the runtime representation of a linear memory. It holds a vector of bytes and an optional
    maximum size, if one was specified at the definition site of the memory.

    meminst ::= {data vec(byte), max u32?}

    The length of the vector always is a multiple of the WebAssembly page size, which is defined to be the constant
    65536 – abbreviated 64Ki. Like in a memory type, the maximum size in a memory instance is given in units of this
    page size.
    The bytes can be mutated through memory instructions, the execution of a data segment, or by external means
    provided by the embedder.
    It is an invariant of the semantics that the length of the byte vector, divided by page size, never exceeds the
    maximum size, if present.

    Attributes:
        limits: limit instance represnt memory size
        size: current size of memory
        data: the content stored in memory
    """

    def __init__(self, limits: structure.Limits):
        self.limits = limits
        self.size = limits.minimum
        self.data = [0] * limits.minimum * 64 * 1024

    def grow(self, n: int):
        if self.limits.maximum and self.size + n > self.limits.maximum:
            raise Exception('Out of memory limit!')
        self.data.extend([0 for _ in range(n * 64 * 1024)])
        self.size += n

    def store(self,addr,len,val):
        self.data[addr:addr+len]=val

class SymbolicMemoryInstance:
    """
    Attributes:
        limits: limit instance represnt memory size
        size: current size of memory
        data: the content stored in memory
    """

    def __init__(self):
        # self.data = z3.Array("memory",z3.BitVecSort(32),z3.BitVecSort(8))
        self.data=dict()

    def store(self,addr,len,val):
        for i in range(len):
            target_addr=z3.simplify(addr+i)
            value=val[i]
            self.data[target_addr]=value
            # self.write_addr.add(target_addr)

    def load(self,addr,len):
        res=[]
        for i in range(len):
            res.append(self[addr+i])
        return res

    def is_symbolic_addr(self,s):
        return s in self.data


    def __getitem__(self,addr):
        # if isinstance(addr,slice):
        #     res=[]
        #     for i in range(addr.start,addr.stop,addr.step):
        #         res.append(self.__getitem__(i))
        #     return res
        addr=z3.simplify(addr)
        print("symbolic addr:",addr)
        if addr not in self.data:
            self.store(addr,1,[z3.BitVec(f'memory_{len(self.data)}',8)])
        # d=z3.Select(self.data,addr)
        d=self.data[addr]
        print("value:",d)
        if utils.is_bv_concrete(d):
            return utils.get_concrete_int(d)
        else:
            return z3.simplify(d)

class GlobalInstance:
    """A global instance is the runtime representation of a global variable. It holds an individual value and a flag
    indicating whether it is mutable.

    globalinst ::= {value val, mut mut}

    The value of mutable globals can be mutated through variable instructions or by external means provided by the
    embedder.

    Attributes:
        value: the value of global instance
        mut: represent the value is mutable of not
    """

    def __init__(self, value: 'Value', mut: bool):
        self.value = value
        self.mut = mut


class ExportInstance:
    """An export instance is the runtime representation of an export. It defines the export’s name and the associated
    external value.

    exportinst ::= {name name, value externval}

    Attributes:
        name: the name of export instance
        value: the value of export instance
    """

    def __init__(self, name: str, value: 'ExternValue'):
        self.name = name
        self.value = value


class ExternValue:
    """An external value is the runtime representation of an entity that can be imported or exported. It is an address
    denoting either a function instance, table instance, memory instance, or global instances in the shared store.

    externval ::= func funcaddr
                | table tableaddr
                | mem memaddr
                | global globaladdr

    Attributes:
        extern_type: the type of extern value, such as varibale, table, function and etc
        addr: the address of extern value
    """

    def __init__(self, extern_type: int, addr: int):
        self.extern_type = extern_type
        self.addr = addr


class Value:
    """Values are represented by themselves.

    Attributes:
        valtype: the type of value, such i32, i64, f32, f64
        n: the truly value
    """

    def __init__(self, valtype: int, n):
        self.valtype = valtype
        self.n = n

    def __repr__(self):
        if utils.is_symbolic(self.n):
            return str(z3.simplify(self.n))
        else:
            return str(self.n)

    @classmethod
    def from_i32(cls, n):
        if utils.is_bv_concrete(n):
            n=utils.get_concrete_int(n)
        elif 'BitVec' in str(n.sort()):
            padding=32-n.size()
            if padding>0:
                n=z3.Concat(z3.BitVecVal(0,padding),n)
        return Value(bin_format.i32, n)

    @classmethod
    def from_i64(cls, n):
        if utils.is_bv_concrete(n):
            n=utils.get_concrete_int(n)
        elif 'BitVec' in str(n.sort()):
            padding=64-n.size()
            if padding>0:
                n=z3.Concat(z3.BitVecVal(0,padding),n)
        return Value(bin_format.i64, n)

    @classmethod
    def from_f32(cls, n):
        return Value(bin_format.f32, n)

    @classmethod
    def from_f64(cls, n):
        return Value(bin_format.f64, n)


class Label:
    """Labels carry an argument arity n and their associated branch target, which is expressed syntactically as an
    instruction sequence:

    label ::= labeln{instr∗}

    Intuitively, instr∗ is the continuation to execute when the branch is taken, in place of the original control
    construct.

    Attributes:
        arity: the number of label
        continuation: the target of branch instruction for current label
    """

    def __init__(self, arity: int, continuation: int):
        self.arity = arity
        self.continuation = continuation

    def __repr__(self):
        return '|'


class Frame:
    """Activation frames carry the return arity of the respective function, hold the values of its locals (including
    arguments) in the order corresponding to their static local indices, and a reference to the function’s own module
    instance:

    activation ::= framen{frame}
    frame ::= {locals val∗, module moduleinst}

    Attributes:
        module: the module of current frame
        locals: the local variables for current frame
        arity: the number of results of current frame
        continuation: the jump target
    """

    def __init__(self, module: 'ModuleInstance', locs: typing.List[Value], arity: int, continuation: int):
        self.module = module
        self.locals = locs
        self.arity = arity
        self.continuation = continuation

    def __repr__(self):
        return '*'
 
    def __deepcopy__(self,memodict={}):
        nf=Frame(self.module,self.locals,self.arity,self.continuation)
        nf.locals=copy.deepcopy(self.locals)
        nf.arity=copy.deepcopy(self.arity)
        nf.continuation=copy.deepcopy(self.continuation)
        return nf


class Stack:
    """Besides the store, most instructions interact with an implicit stack. The stack contains three kinds of entries:

    Values: the operands of instructions.
    Labels: active structured control instructions that can be targeted by branches.
    Activations: the call frames of active function calls.

    These entries can occur on the stack in any order during the execution of a program. Stack entries are described
    by abstract syntax as follows.

    Attributes:
        data: the content of stack
    """

    def __init__(self):
        self.data = []
        self.frame_len = 0 #记录当前栈帧中的元素个数

    def __repr__(self):
        return self.data.__repr__()

    def add(self, e):
        self.data.append(e)
        if isinstance(e,Frame):
            self.frame_len = 0
        elif isinstance(e,Label):
            pass
        else:
            self.frame_len += 1

    def ext(self, e: typing.List):
        for i in e:
            self.add(i)

    def pop(self):
        if len(self.data)==0:
            #因为brach和loop的长度限制处理时的强制跳出，这里也可能会遇到没有数据仍然需要pop的情况
            #就当是增加鲁棒性了
            return "114514"
        e=self.top()
        if isinstance(e,Frame):
            self.frame_len = 0
            for i in range(1,len(self.data)):
                if isinstance(self.data[-1-i],Label):
                    pass
                elif isinstance(self.data[-1-i],Frame):
                    break
                else:
                    self.frame_len += 1
        elif isinstance(e,Label):
            pass
        else:
            self.frame_len -= 1
        return self.data.pop()

    def len(self):
        return len(self.data)

    def top(self):
        return self.data[-1]

    def status(self):
        for i in range(len(self.data)):
            i = -1 - i
            if isinstance(self.data[i], Label):
                return Label
            if isinstance(self.data[i], Frame):
                return Frame


class Ctx:
    """This exposes the specified memory of the WebAssembly instance.

    Attributes:
        mems: memory instance
    """

    def __init__(self, mems: typing.List[MemoryInstance]):
        self.mems = mems
