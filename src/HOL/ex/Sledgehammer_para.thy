theory Sledgehammer_para
  imports "~~/src/HOL/Sledgehammer"
begin

sledgehammer[parallel_subgoals]

lemma assumes A B C D E
      shows "A \<and> B \<and> C \<and> D \<and> E \<and> F"
 apply (intro conjI)
 sledgehammer
 sledgehammer[stop_on_first]
 sledgehammer[stop_on_first, parallel_subgoals] 4
                               \<comment> \<open>TODO: show the full reconstruction proof
                                         whenever @{command sledgehammer} succeeds on all subgoals.\<close>
 sledgehammer[stop_on_first, parallel_subgoals] 6
 sledgehammer[parallel_subgoals]
oops

end