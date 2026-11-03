module

public import ElboimSly.Frozen.Theorems.ExistsUniqueTrajectories
public import ElboimSly.Frozen.Theorems.InterchangePiBijective
public import ElboimSly.Frozen.Theorems.PoissonKmtCoupling
public import ElboimSly.Frozen.Theorems.X1ThetaCoupling
public import ElboimSly.Frozen.Theorems.IndMain
public import ElboimSly.Frozen.Theorems.RootR1
public import ElboimSly.Frozen.Theorems.RootR2

/-!
# Axiom audit

Run `lake env lean ElboimSlyChallenges/ElboimSly/AxiomsAudit.lean > axioms.log 2>&1` and check the log
with `python3 scripts/check_axioms.py axioms.log ElboimSlyChallenges/ElboimSly/AxiomsAudit.lean`.
-/

#print axioms ElboimSly.existsUnique_trajectories
#print axioms ElboimSly.interchangePi_bijective
#print axioms ElboimSly.poisson_kmt_coupling
#print axioms ElboimSly.x1theta_coupling
#print axioms ElboimSly.ind_main
#print axioms ElboimSly.root_R1
#print axioms ElboimSly.root_R2
