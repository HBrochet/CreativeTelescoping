(* What follows is functionality that should (already) be exported by Mgfun. *)

(* At this stage, cannot be avoided. *)
kernelopts(opaquemodules = false):

GB_to_matrices := proc(GB, MOrd, subs_set, $)
  local back_subs, Alg, dvs, J, B, rev, i, ca, dvar, Dvar, _Dvar,
    var, _var, tvar, matrices, action;
  Alg := MOrd["algebra"];
  dvs := Alg["non_inv_right_indets"];
  J := Groebner:-LeadingMonomial(GB, MOrd);
  B, rev := Groebner:-NormalSet(J, MOrd["CreationArguments"][2]);
  for i to nops(dvs) do
    dvar := dvs[i];
    Dvar :=
      Mgfun:-NonCommutativeMultiplicationMatrix(Alg, dvar, B, rev, GB, MOrd);
    (* Propose multiple indexations, to choose from by the user depending
       on their need to use the basis B.
       Each ca is of the form ty[i] = [dv[i], x[i]]. *)
    matrices[dvar] := Dvar;
    ca := op(select(has,
      Alg["CreationArguments"][1]["CreationArguments"][4], dvar));
    var := op([2, 2], ca);
    tvar[i] := var :: op(1, ca);
    matrices[tvar[i]] := Dvar;
    action[i] := subs({_var = var, _Dvar = eval(Dvar)},
      proc(V, $) (_Dvar . V + map(diff, V, _var)) end);
    action[var] := action[i]
  od;
  Record(
    ':-gbasis' = GB,
    ':-ordering' = MOrd,
    ':-algebra' = Alg,
    ':-basis' = B,
    ':-basis_rev' = rev,
    ':-matrices' = subs(subs_set, eval(matrices)),
    ':-action' = eval(action),
    ':-subs_set' = subs_set,
    ':-back_subs' = {seq(op(2, i) = op(1, i), i = subs_set)},
    ':-typed_vars' = [seq(tvar[i], i = 1..nops(dvs))]
  )
end:

dfinite_expr_to_matrices := proc(expr, typed_vars, $)
  local GB, MOrd, subs_set;
  GB, MOrd, subs_set :=
    Mgfun:-MG_Internals:-expression_to_system(expr, typed_vars);
  GB_to_matrices(GB, MOrd, subs_set)
end:

LFSol_to_matrices := proc(lfs, typed_vars, $)
  local us := Mgfun:-MG_Internals:-recognize_operator_algebra(op(lfs));
  local dvar := us["algebra"]["CreationArguments"][1]["CreationArguments"][3];
  local MOrd := Groebner:-MonomialOrder(us["algebra"], tdeg(op(dvar)));
  local mm := GB_to_matrices(Groebner:-Basis(us["system"], MOrd), MOrd, {});
  local typed_vars_recognized :=
    map(q -> op([2,2], q) :: op(1, q),
      mm:-algebra["CreationArguments"][1]["CreationArguments"][4]);
  if typed_vars_recognized <> typed_vars_recognized then
    error "failure to recognize wanted commutations"
  fi;
  mm
end:

LFSol_of_multi_hyper := proc(expr, typed_vars, $)
  local tv, var, ty, _f;
  local vars := map2(op, 1, convert(typed_vars, list));
  local the_f := _f(op(vars));
  local sys := table();
  for tv in typed_vars do
    var, ty := op(tv);
    if ty = diff then
      sys[tv] := diff(the_f, var) - normal(diff(expr, var) / expr) * the_f
    elif ty = shift then
      sys[tv] := subs(var = var + 1, the_f)
        - normal(subs(var = var + 1, expr) / expr, expanded) * the_f
    else
      error
    fi
  od;
  LFSol({seq(sys[tv], tv = typed_vars)})
end:
