(* Author: Tobias Nipkow *)

theory Tree_Real
imports
  Complex_Main
  Tree
begin

text \<open>
  This theory is separate from @{theory "HOL-Library.Tree"} because the former is discrete and
  builds on @{theory Main} whereas this theory builds on @{theory Complex_Main}.
\<close>


lemma size1_height_log: "log 2 (size1 t) \<le> height t"
by (simp add: log2_of_power_le size1_height)

lemma min_height_size1_log: "min_height t \<le> log 2 (size1 t)"
by (simp add: le_log2_of_power min_height_size1)

lemma size1_log_if_complete: "complete t \<Longrightarrow> height t = log 2 (size1 t)"
by (simp add: log2_of_power_eq size1_if_complete)

lemma min_height_size1_log_if_incomplete:
  "\<not> complete t \<Longrightarrow> min_height t < log 2 (size1 t)"
by (simp add: less_log2_of_power min_height_size1_if_incomplete)


lemma min_height_balanced: assumes "balanced t"
shows "min_height t = nat(floor(log 2 (size1 t)))"
proof cases
  assume *: "complete t"
  hence "size1 t = 2 ^ min_height t"
    by (simp add: complete_iff_height size1_if_complete)
  from log2_of_power_eq[OF this] show ?thesis by linarith
next
  assume *: "\<not> complete t"
  hence "height t = min_height t + 1"
    using assms min_height_le_height[of t]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size1 t < 2 ^ (min_height t + 1)"
    by (metis * size1_height_if_incomplete)
  hence "log 2 (size1 t) < min_height t + 1"
    using log2_of_power_less size1_ge0 by blast
  thus ?thesis using min_height_size1_log[of t] by linarith
qed

lemma height_balanced: assumes "balanced t"
shows "height t = nat(ceiling(log 2 (size1 t)))"
proof cases
  assume *: "complete t"
  hence "size1 t = 2 ^ height t"
    by (simp add: size1_if_complete)
  from log2_of_power_eq[OF this] show ?thesis
    by linarith
next
  assume *: "\<not> complete t"
  hence **: "height t = min_height t + 1"
    using assms min_height_le_height[of t]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size1 t \<le> 2 ^ (min_height t + 1)" by (metis size1_height)
  from  log2_of_power_le[OF this size1_ge0] min_height_size1_log_if_incomplete[OF *] **
  show ?thesis by linarith
qed

lemma balanced_Node_if_wbal1:
assumes "balanced l" "balanced r" "size l = size r + 1"
shows "balanced \<langle>l, x, r\<rangle>"
proof -
  from assms(3) have [simp]: "size1 l = size1 r + 1" by(simp add: size1_def)
  have "nat \<lceil>log 2 (1 + size1 r)\<rceil> \<ge> nat \<lceil>log 2 (size1 r)\<rceil>"
    by(rule nat_mono[OF ceiling_mono]) simp
  hence 1: "height(Node l x r) = nat \<lceil>log 2 (1 + size1 r)\<rceil> + 1"
    using height_balanced[OF assms(1)] height_balanced[OF assms(2)]
    by (simp del: nat_ceiling_le_eq add: max_def)
  have "nat \<lfloor>log 2 (1 + size1 r)\<rfloor> \<ge> nat \<lfloor>log 2 (size1 r)\<rfloor>"
    by(rule nat_mono[OF floor_mono]) simp
  hence 2: "min_height(Node l x r) = nat \<lfloor>log 2 (size1 r)\<rfloor> + 1"
    using min_height_balanced[OF assms(1)] min_height_balanced[OF assms(2)]
    by (simp)
  have "size1 r \<ge> 1" by(simp add: size1_def)
  then obtain i where i: "2 ^ i \<le> size1 r" "size1 r < 2 ^ (i + 1)"
    using ex_power_ivl1[of 2 "size1 r"] by auto
  hence i1: "2 ^ i < size1 r + 1" "size1 r + 1 \<le> 2 ^ (i + 1)" by auto
  from 1 2 floor_log_nat_eq_if[OF i] ceiling_log_nat_eq_if[OF i1]
  show ?thesis by(simp add:balanced_def)
qed

lemma balanced_sym: "balanced \<langle>l, x, r\<rangle> \<Longrightarrow> balanced \<langle>r, y, l\<rangle>"
by(auto simp: balanced_def)

lemma balanced_Node_if_wbal2:
assumes "balanced l" "balanced r" "abs(int(size l) - int(size r)) \<le> 1"
shows "balanced \<langle>l, x, r\<rangle>"
proof -
  have "size l = size r \<or> (size l = size r + 1 \<or> size r = size l + 1)" (is "?A \<or> ?B")
    using assms(3) by linarith
  thus ?thesis
  proof
    assume "?A"
    thus ?thesis using assms(1,2)
      apply(simp add: balanced_def min_def max_def)
      by (metis assms(1,2) balanced_optimal le_antisym le_less)
  next
    assume "?B"
    thus ?thesis
      by (meson assms(1,2) balanced_sym balanced_Node_if_wbal1)
  qed
qed

lemma balanced_if_wbalanced: "wbalanced t \<Longrightarrow> balanced t"
proof(induction t)
  case Leaf show ?case by (simp add: balanced_def)
next
  case (Node l x r)
  thus ?case by(simp add: balanced_Node_if_wbal2)
qed

end
