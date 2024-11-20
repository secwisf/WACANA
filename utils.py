#!/usr/bin/python3
# -*- coding: utf-8 -*-
"""
The utils module includes functions to help symbolic execution, such as transformation function 
for transform truly value to symbolic value and versa.
"""
import ctypes
from typing import Union
import six
import z3
import bin_format


def is_int(value: int) -> bool:
    return isinstance(value, six.integer_types)


def is_float(value: float) -> bool:
    return isinstance(value, float)


def is_symbolic(value: Union[float, int, z3.BitVecNumRef]) -> bool:
    return not isinstance(value, six.integer_types) and not isinstance(value, float) and not isinstance(value, int) and not is_bv_concrete(value)

def is_bv_concrete(bv):
    if isinstance(bv, six.integer_types) or isinstance(bv, float) or isinstance(bv, int):
        return True
    try:
        hex(z3.simplify(bv).as_long())
        return True
    except AttributeError as e:
        return False
    except Exception:
        raise Exception("pdb")



def is_all_real(*args) -> bool:
    for elem in args:
        if is_symbolic(elem):
            return False
    return True


def to_symbolic(number: int, length: int) -> z3.BitVecVal:
    if is_int(number) or is_float(number):
        return z3.BitVecVal(number, length)
    return number


def to_signed(number: int, length: int) -> int:
    if number > 2**(length - 1):
        return (2 ** length - number) * (-1)
    else:
        return number


def to_unsigned(number: int, length: int) -> int:
    if number < 0:
        return number + 2 ** length
    else:
        return number


def sym_abs(x):
    return z3.If(x >= 0, x, -x)


def check_sat(solver: z3.Solver, pop_if_exception: bool = True) -> z3.CheckSatResult:
    try:
        ret = solver.check()
        if ret == z3.unknown:
            raise z3.Z3Exception(solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            solver.pop()
        raise e
    return ret


def eos_abi_to_int(abi_name: str) -> int:
    if len(abi_name) > 13:
        raise Exception('string is too long to be a valid name')
    if not abi_name:
        return 0
    value = 0
    n = min(len(abi_name), 12)
    for i in range(n):
        value <<= 5
        value |= _char_to_value(abi_name[i])
    value <<= (4 + 5*(12-n))
    if len(abi_name) == 13:
        v = _char_to_value(abi_name[12])
        if v > 0x0F:
            raise Exception('13th character in name cannot be a letter that comes after j')
        value |= v
    return ctypes.c_int64(value).value

def eos_int_to_abi(abi: int) -> str:
    charmap=".12345abcdefghijklmnopqrstuvwxyz"
    res=[ord(' ')]*13
    tmp=abi
    for i in range(13):
        c=charmap[tmp&(0x0f if i==0 else 0x1f)]
        res[12-i]=c;
        tmp>>=(4 if i==0 else 5)
    return ''.join(res).rstrip('.')


def _char_to_value(c: str) -> int:
    if c == '.':
        return 0
    elif '1' <= c <= '5':
        return (ord(c) - ord('1')) + 1
    elif 'a' <= c <= 'z':
        return (ord(c) - ord('a')) + 6
    else:
        raise Exception('character is not in allowed character set for names')


def gen_transfer_symbolic_args(func: 'instance.FunctionInstance'):
    symbolic_params = []
    argc=len(func.functype.args)
    for i in range(argc-3):
        e=func.functype.args[i]
        if e == bin_format.i32:
            symbolic_params.append(z3.BitVec(f'i32_arg_bv_{i}', 32))
        elif e == bin_format.i64:
            symbolic_params.append(z3.BitVec(f'i64_arg_bv_{i}', 64))
        else:
            symbolic_params.append(z3.FP(f'f64_{i}', z3.Float64()))
    symbolic_params.extend([eos_abi_to_int("vaults.sx"),eos_abi_to_int("vaults.sx"),eos_abi_to_int("transfer")])
    #这里要改，不能固定参数
    return symbolic_params


def gen_symbolic_args(func: 'instance.FunctionInstance'):
    symbolic_params = []
    for i, e in enumerate(func.functype.args):
        if e == bin_format.i32:
            symbolic_params.append(z3.BitVec(f'i32_input_{i}', 32))
        elif e == bin_format.i64:
            symbolic_params.append(z3.BitVec(f'i64_input_{i}', 64))
        elif e == bin_format.f32:
            # f32_bv = z3.BitVec(f'f32_bv_{i}', 32)
            # symbolic_params.append(z3.fpBVToFP(f32_bv, z3.Float32()))
            # another approach
            symbolic_params.append(z3.FP(f'f32_input_{i}', z3.Float32()))
        else:
            # f64_bv = z3.BitVec(f'f64_bv_{i}', 64)
            # symbolic_params.append(z3.fpBVToFP(f64_bv, z3.Float64()))
            # another approach
            symbolic_params.append(z3.FP(f'f64_input_{i}', z3.Float64()))
    return symbolic_params


def gen_symbolic_value(var_type, name):
    if var_type == bin_format.i32:
        return z3.BitVec(name, 32)
    if var_type == bin_format.i64:
        return z3.BitVec(name, 64)
    if var_type == bin_format.f32:
        return z3.FP(f'f32_{name}', z3.Float32())
    if var_type == bin_format.f64:
        return z3.FP(f'f64_{name}', z3.Float64())
    raise TypeError('Unsupported variable type')

def get_concrete_int(item):
    if type(item) == int:
        return item
    if type(item) == z3.BitVecNumRef:
        return item.as_long()
    return z3.simplify(item).as_long()

def get_concrete_int_from_bytes(_bytes, start_index):
    return int.from_bytes(_bytes[start_index:start_index + 32], byteorder='litter')


def convert_concrete_int_to_bytes(val):
    if type(val) == int:
        return val.to_bytes(32, byteorder='litter')
    return (z3.simplify(val).as_long()).to_bytes(32, byteorder='litter')

