# maxsat_solve

maxsat_solve is a treewidth-guided MaxSAT-solver written in Rust that was developed as part of a master thesis at the Universität zu Lübeck. This solver implements FPT-algorithms for MaxSAT using primal, dual, and incidence tree decompositions for constructing solutions. 

## Build the solver

To build the solver you first need to install the [Rust toolchain](https://www.rust-lang.org/). After installation run the following commands:
```bash
$ git clone https://github.com
$ cd maxsat_solve
$ cargo build --release
```

The binary can then be found at ```./target/release/maxsat_solve```.

## Using the solver

The solver takes as input a file in the WCNF-format. If the file is gzip-compressed you can add the ```-c``` flag to pass the file without decompressing it first. By default the solver will use an incidence tree decomposition. You can choose another type by using the flag ```-p``` for primal, ```-d``` for dual, and ```-i``` for incidence tree decompositions. The optional ```-t``` flag can be used for double-checking the computed score of the final variable assignment. If you omit the ```-f``` flag the input will be read directly from STDIN.

To run the compiled binary run the following command:

```bash
$ maxsat_solve -f /path/to/WCNF [-p|-d|-i] [-c] [-t]
```