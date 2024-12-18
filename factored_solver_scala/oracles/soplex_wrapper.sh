soplex --loadset="oracles/exact.set" -X -Y isabelle_problem.lp | sed -e '1,/Primal/d' | sed '/All/d' | sed '/Dual/s/.*/DUAL/' > isabelle_sol.sol
