module Bug1270

open FStar.Tactics

#set-options "--admit_smt_queries true" // VC.. ugh

let test =
  assert_by_tactic (True ==> True)
    (fun () ->
        (fun () ->
          let _ = forall_intros () in
          let env = cur_env () in
          let hyps = binders_of_env env in
          match hyps with
          | [] -> ()
          | h :: _ -> ()) `or_else` trivial)
