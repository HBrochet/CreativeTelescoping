macro(translate=PolynomialTools['Translate']);


CreativeTelescoping:=module()

option package;

export EvalCert, testcert, hypergeomtosum, SingularitiesCertificate;

local ModuleApply, really_lose_info_I_mean_it, _ORDMAX, redctint, redctsum, scalar_red_ct, removeshell,
adjoint, cyclic_vec, try_cyclic_vec, certif_lagrange_v, scalar_red_ct_int, adjoint_diff, adjoint_shift,
GB_to_matrices, dfinite_expr_to_matrices, LFSol_to_matrices, LFSol_of_multi_hyper,
scalar_red_ct_sum, cyclic_vec_sum, try_cyclic_vec_sum, InitRed, Reduction, ComputeBasis,
ComputeBasisSR, addlistSRP, ComputeBasisSRP, weakreduction, weakreducpol, strongreduction,
strongreducpol, MyShiftlessDecFact, rnd, MyShiftlessDecIrred, RootDifferInt, IndEqInfty,
valpol2, certif_lagrange, valpol, intsols, indicialeq0, indicialeq0inf, indicialeq1, splitpol,
zeroshift, applydop, checkcert, rembezout, customgcdex, localreduction_base, localreduction,
hermitered0, hermitered1, hermitered, exceptionalbasis, echelonpols, redmodpols, redmodfracs,
reduction, PfracAction, Dmon, MulPfrac, CanonicalFormToRat, splitdenom, TestCanonicalForm,
RowEchelonForm, SplitFrac, evalLcert, evalL, ShiftlessDecIrred, NormalizePfracElement,
ExtractPolynomialPart,StrongReduction, WeakReduction, LocalReduction, ReductionPolynomial,
factpol,singpolmul, internal_test_cert, normaldag, splitlist,cyclic_vec_shift,try_cyclic_vec_shift;

$include<Mgfun_missing.mpl>

$include<redct.mpl>
$include<redctsum.mpl>
$include<red_difference_op.mpl>
$include<red.mpl>


ModuleApply := proc(sumorint,alg,{certificate :: name:=NULL,LFSolbasis :: name :=NULL})
    if op(0,sumorint) = 'Sum' then 
        return redctsum(sumorint,alg,_options);
    elif op(0,sumorint) = 'Int' then 
        return redctint(sumorint,alg);
    else
        error "The input is not a sum or an integral.";
    fi;
end:

end module;