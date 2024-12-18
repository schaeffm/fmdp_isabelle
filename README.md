# Factored MDPs in Isabelle/HOL

## Description
This is a formalization of Factored Markov Decision Processes in the interactive theorem prover Isabelle/HOL.
We provide
- a formalization of Factored MDPs + translation to explicit MDPs (in `./isabelle/algorithm`)
- a formalization of the Factored Approximate Policy Iteration algorithm (in `./isabelle/algorithm`)
- a certificate checker for linear programming solutions (in `./isabelle/code/lp_cert)
- an executable version of the algorithm (in `./isabelle/code`)
- a wrapper Scala program that allows to define custom domains and calls the verified solver (in `./factored_solver_scala`)

### Installation
- make sure a a *Java Runtime Environment* is installed (we use openjdk 17.0.10)
- install the LP solver ([Soplex / SCIP](https://scipopt.org/index.php#download)
- select SCIP version 9.0.1, Soplex version 7.0.1
- add Soplex to your path, e.g. `export PATH="path/to/SCIP/SCIPOptSuite-9.0.1-Linux/bin:$PATH"`
- make sure you can execute `soplex` on the command line
- this may require installing the dependencies listed on the website, e.g. libopenblas-dev, gcc, libtbb12
- ensure `./factored_solver_scala/oracles/soplex_wrapper.sh` is executable.
- the installation was tested on Ubuntu 23.10.

### Usage
We ship the executable `factored_solver_scala/factored_solvers_scala.jar`.
It requires 

In the folder `factored_solver_scala`, execute the command `java -Xss128M -jar factored_solver_scala.jar ring 7 1/100 9/10 100`. 
This will execute the solver on the *Ring* domain, with 7 machines, an error bound of 0.01, a discount factor of 0.9 and a timeout of 100 iterations.

## Building the Project

### Code Export from Isabelle (optional)
We provide the Scala code that Isabelle exports, so these steps are optional:
1. Install *Isabelle 2023* (follow the [instructions](https://isabelle.in.tum.de/installation.html)).
2. Add the *AFP* for Isabelle 2023 to your Isabelle installation ([instructions](https://www.isa-afp.org/help/)).
3. Add isabelle to your `PATH` environment variable (the directory `/path/to/isabelle/Isabelle2023/bin`).
4. Install LaTeX (lualatex) for document export. 
5. Export the Scala code yourself with the script `./build_and_export.sh`.
This may take long (20+ minutes) on a fresh install of Isabelle.

### Building the Solver
Building the project also requires Scala and sbt to be installed.
1. Install the *Scala* compiler (version 2.13.12).
2. Install *sbt* (version 1.10.0) on your system.
3. Build + execute the solver from the folder `factored_solver_scala` with the command `sbt -J-Xss128M "run <domain> <machines> <error_bound> <discount_factor> <timeout>".

## Defining Custom Domains
- The ring domain is defined in `./factored_solver_scala/src/main/scala/Model_Ring.scala`.
- The star domain is defined in `./factored_solver_scala/src/main/scala/Model_Star.scala`.
- The input to the solver is an object of the class `FactoredMDP`, as defined in e.g. `./factored_solver_scala/src/main/scala/Model_Ring.scala`.
