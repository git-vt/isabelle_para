theory Sledgehammer_para
  imports "~~/src/HOL/Sledgehammer"
begin

sledgehammer[parallel_subgoals] \<comment> \<open>The default warning is raised as usual
                                    (no matter the list of options we provide).\<close>

lemma assumes A B (*C*) D E F G (*H*)
      shows "A \<and> B \<and> C \<and> D \<and> E \<and> F \<and> G \<and> H"
 apply (intro conjI)
 sledgehammer
 sledgehammer[stop_on_first]
 sledgehammer[stop_on_first, parallel_subgoals] 2
 sledgehammer[stop_on_first, parallel_subgoals] 8
 sledgehammer[parallel_subgoals]
 sledgehammer[parallel_subgoals, join_subgoals, verbose]
  \<comment> \<open>TODO: show the full reconstruction proof whenever @{command sledgehammer} is generating
            consecutive proofs of subgoals transitioning from the Isar VM prove to Isar VM state
            (and vice-versa).\<close>
oops

sledgehammer_params[parallel_subgoals, join_subgoals]

end