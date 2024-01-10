import re
from .maude import *

def indented_str(s: str, indent: int):
    li = [" " for _ in range(indent)]
    li.append(s)
    return "".join(li)


def id_gen():
    count = 0
    while True:
        yield count
        count += 1


def get_symbol_info(module: Module):
    if module is None:
        return dict()
    
    symbol_info = dict()
    symbols = module.getSymbols()
    for symbol in symbols:
        decls = symbol.getOpDeclarations()
        user_symb = str(symbol)
        for n, decl in enumerate(decls):
            meta = symbol.getMetadata(n)
            if meta is None or "smt" not in meta:
                continue

            if "euf" in meta:
                sorts = tuple([str(s) for s in decl.getDomainAndRange()])
                
                key = (user_symb, sorts)
                if key not in symbol_info:
                    symbol_info[key] = ("euf", None)
                else:
                    print(f"ambiguous symbol found during symbol info creation ({user_symb} with {symbol_info[0]}:{symbol_info[1]})")
                
            else:
                p_l = meta.split(" ")

                if len(p_l) != 2:
                    raise Exception("incorrect metadata")
                
                if p_l[0] != "smt":
                    raise Exception("incorrect metadata (should be started with \"smt\")")
                
                # theory:symbol
                ts = p_l[1].split(":")
                
                if len(ts) != 2:
                    raise Exception(f"unsupported theory and symbol metadata ({p_l[1]})")
                
                theory, symb = ts
                sorts = tuple([str(s) for s in decl.getDomainAndRange()])

                key = (user_symb, sorts)
                if key not in symbol_info:
                    symbol_info[key] = (theory, symb)
                else:
                    print(f"ambiguous symbol found during symbol info creation ({user_symb} with {symbol_info[0]}:{symbol_info[1]})")

    return symbol_info