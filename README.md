# Retro

To run the prototype tool use the script:
```
$ ./runtool <eq.smt>
```
or explicitly:
```
$ python3 rmc-solve.py <eq.smt> ../automata/rrt-x-yx-len.vtf ../automata/rrt-x-eps-len.vtf ../automata/rrt-x-yx.vtf ../automata/rrt-x-eps.vtf
```
where `eq.smt` is equation in smt-lib2 format.

## Install
The tool requires Python of version 3.7.3 or higher. In addition it requires the following packages and libraries:
 - Python package `FAdo`; this you may install using
 ```
 $ pip3 install -r requirements.txt
 ```
 - VATA library with Python binding; this you may install using the following steps
 ```
 $ git clone -b pybind https://github.com/ondrik/libvata2.git
 ```
 To compile VATA use
 ```
 $ make release
 ```
 After a successful compilation, copy library from VATA's directory
 `build/python_bind/libvata2-c-ifc` into `lib` directory in the root directory
 of Retro (you need to create this directory). Additionaly you may need to set
 `LD_LIBRARY_PATH` to this directory.

## Experiments & Tool Settings

The tool contains heuristics that can be turn of/off in the file `RetroConfig.py` (we call it `H`). The config file contains also selection of automata library (FAdo or VATA). For the following benchmarks we also provide recommended heuristics config.

The repository contains also benchmarks:
 - `Kepler22` benchmarks (`¬H`),
 - formulas obtained from `kazula` benchmars (`H`), and
 - formulas obtained from `pyex` benchmarks (`H`).

To run experiments on a directory with smt files, use `experimental/experimental.py`.
