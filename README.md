Maude-SE is an SMT extension of [Maude](https://github.com/SRI-CSL/Maude). It provides a symbolic SMT search and satisfiability checking for SMT formulas. Currently supported SMT solvers are Z3, Yices2, and CVC5.

## Building

We provide a building script, `build.sh`. You can simply build Maude-SE as follows:

```
./build.sh maude-se
```

The script creates an `out` directory at the top directory and stores the built product (a python wheel) in it.
Then, use the following command to install the wheel:
```
pip install ./out/*.whl
```