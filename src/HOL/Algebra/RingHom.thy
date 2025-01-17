(*  Title:      HOL/Algebra/RingHom.thy
    Author:     Stephan Hohe, TU Muenchen
*)

theory RingHom
imports Ideal
begin

section \<open>Homomorphisms of Non-Commutative Rings\<close>

text \<open>Lifting existing lemmas in a \<open>ring_hom_ring\<close> locale\<close>
locale ring_hom_ring = R?: ring R + S?: ring S
    for R (structure) and S (structure) +
  fixes h
  assumes homh: "h \<in> ring_hom R S"
  notes hom_mult [simp] = ring_hom_mult [OF homh]
    and hom_one [simp] = ring_hom_one [OF homh]

sublocale ring_hom_cring \<subseteq> ring: ring_hom_ring
  by standard (rule homh)

sublocale ring_hom_ring \<subseteq> abelian_group?: abelian_group_hom R S
apply (intro abelian_group_homI R.is_abelian_group S.is_abelian_group)
apply (intro group_hom.intro group_hom_axioms.intro R.a_group S.a_group)
apply (insert homh, unfold hom_def ring_hom_def)
apply simp
done

lemma (in ring_hom_ring) is_ring_hom_ring:
  "ring_hom_ring R S h"
  by (rule ring_hom_ring_axioms)

lemma ring_hom_ringI:
  fixes R (structure) and S (structure)
  assumes "ring R" "ring S"
  assumes (* morphism: "h \<in> carrier R \<rightarrow> carrier S" *)
          hom_closed: "!!x. x \<in> carrier R ==> h x \<in> carrier S"
      and compatible_mult: "\<And>x y. [| x \<in> carrier R; y \<in> carrier R |] ==> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
      and compatible_add: "\<And>x y. [| x \<in> carrier R; y \<in> carrier R |] ==> h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
      and compatible_one: "h \<one> = \<one>\<^bsub>S\<^esub>"
  shows "ring_hom_ring R S h"
proof -
  interpret ring R by fact
  interpret ring S by fact
  show ?thesis apply unfold_locales
apply (unfold ring_hom_def, safe)
   apply (simp add: hom_closed Pi_def)
  apply (erule (1) compatible_mult)
 apply (erule (1) compatible_add)
apply (rule compatible_one)
done
qed

lemma ring_hom_ringI2:
  assumes "ring R" "ring S"
  assumes h: "h \<in> ring_hom R S"
  shows "ring_hom_ring R S h"
proof -
  interpret R: ring R by fact
  interpret S: ring S by fact
  show ?thesis apply (intro ring_hom_ring.intro ring_hom_ring_axioms.intro)
    apply (rule R.is_ring)
    apply (rule S.is_ring)
    apply (rule h)
    done
qed

lemma ring_hom_ringI3:
  fixes R (structure) and S (structure)
  assumes "abelian_group_hom R S h" "ring R" "ring S" 
  assumes compatible_mult: "\<And>x y. [| x \<in> carrier R; y \<in> carrier R |] ==> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
      and compatible_one: "h \<one> = \<one>\<^bsub>S\<^esub>"
  shows "ring_hom_ring R S h"
proof -
  interpret abelian_group_hom R S h by fact
  interpret R: ring R by fact
  interpret S: ring S by fact
  show ?thesis apply (intro ring_hom_ring.intro ring_hom_ring_axioms.intro, rule R.is_ring, rule S.is_ring)
    apply (insert group_hom.homh[OF a_group_hom])
    apply (unfold hom_def ring_hom_def, simp)
    apply safe
    apply (erule (1) compatible_mult)
    apply (rule compatible_one)
    done
qed

lemma ring_hom_cringI:
  assumes "ring_hom_ring R S h" "cring R" "cring S"
  shows "ring_hom_cring R S h"
proof -
  interpret ring_hom_ring R S h by fact
  interpret R: cring R by fact
  interpret S: cring S by fact
  show ?thesis by (intro ring_hom_cring.intro ring_hom_cring_axioms.intro)
    (rule R.is_cring, rule S.is_cring, rule homh)
qed


subsection \<open>The Kernel of a Ring Homomorphism\<close>

\<comment> \<open>the kernel of a ring homomorphism is an ideal\<close>
lemma (in ring_hom_ring) kernel_is_ideal:
  shows "ideal (a_kernel R S h) R"
apply (rule idealI)
   apply (rule R.is_ring)
  apply (rule additive_subgroup.a_subgroup[OF additive_subgroup_a_kernel])
 apply (unfold a_kernel_def', simp+)
done

text \<open>Elements of the kernel are mapped to zero\<close>
lemma (in abelian_group_hom) kernel_zero [simp]:
  "i \<in> a_kernel R S h \<Longrightarrow> h i = \<zero>\<^bsub>S\<^esub>"
by (simp add: a_kernel_defs)


subsection \<open>Cosets\<close>

text \<open>Cosets of the kernel correspond to the elements of the image of the homomorphism\<close>
lemma (in ring_hom_ring) rcos_imp_homeq:
  assumes acarr: "a \<in> carrier R"
      and xrcos: "x \<in> a_kernel R S h +> a"
  shows "h x = h a"
proof -
  interpret ideal "a_kernel R S h" "R" by (rule kernel_is_ideal)

  from xrcos
      have "\<exists>i \<in> a_kernel R S h. x = i \<oplus> a" by (simp add: a_r_coset_defs)
  from this obtain i
      where iker: "i \<in> a_kernel R S h"
        and x: "x = i \<oplus> a"
      by fast+
  note carr = acarr iker[THEN a_Hcarr]

  from x
      have "h x = h (i \<oplus> a)" by simp
  also from carr
      have "\<dots> = h i \<oplus>\<^bsub>S\<^esub> h a" by simp
  also from iker
      have "\<dots> = \<zero>\<^bsub>S\<^esub> \<oplus>\<^bsub>S\<^esub> h a" by simp
  also from carr
      have "\<dots> = h a" by simp
  finally
      show "h x = h a" .
qed

lemma (in ring_hom_ring) homeq_imp_rcos:
  assumes acarr: "a \<in> carrier R"
      and xcarr: "x \<in> carrier R"
      and hx: "h x = h a"
  shows "x \<in> a_kernel R S h +> a"
proof -
  interpret ideal "a_kernel R S h" "R" by (rule kernel_is_ideal)
 
  note carr = acarr xcarr
  note hcarr = acarr[THEN hom_closed] xcarr[THEN hom_closed]

  from hx and hcarr
      have a: "h x \<oplus>\<^bsub>S\<^esub> \<ominus>\<^bsub>S\<^esub>h a = \<zero>\<^bsub>S\<^esub>" by algebra
  from carr
      have "h x \<oplus>\<^bsub>S\<^esub> \<ominus>\<^bsub>S\<^esub>h a = h (x \<oplus> \<ominus>a)" by simp
  from a and this
      have b: "h (x \<oplus> \<ominus>a) = \<zero>\<^bsub>S\<^esub>" by simp

  from carr have "x \<oplus> \<ominus>a \<in> carrier R" by simp
  from this and b
      have "x \<oplus> \<ominus>a \<in> a_kernel R S h" 
      unfolding a_kernel_def'
      by fast

  from this and carr
      show "x \<in> a_kernel R S h +> a" by (simp add: a_rcos_module_rev)
qed

corollary (in ring_hom_ring) rcos_eq_homeq:
  assumes acarr: "a \<in> carrier R"
  shows "(a_kernel R S h) +> a = {x \<in> carrier R. h x = h a}"
  apply rule defer 1
   apply clarsimp defer 1
proof
  interpret ideal "a_kernel R S h" "R" by (rule kernel_is_ideal)

  fix x
  assume xrcos: "x \<in> a_kernel R S h +> a"
  from acarr and this
  have xcarr: "x \<in> carrier R"
    by (rule a_elemrcos_carrier)

  from xrcos
  have "h x = h a" by (rule rcos_imp_homeq[OF acarr])
  from xcarr and this
  show "x \<in> {x \<in> carrier R. h x = h a}" by fast
next
  interpret ideal "a_kernel R S h" "R" by (rule kernel_is_ideal)

  fix x
  assume xcarr: "x \<in> carrier R"
    and hx: "h x = h a"
  from acarr xcarr hx
  show "x \<in> a_kernel R S h +> a" by (rule homeq_imp_rcos)
qed

lemma (in ring_hom_ring) nat_pow_hom:
  "x \<in> carrier R \<Longrightarrow> h (x [^] (n :: nat)) = (h x) [^]\<^bsub>S\<^esub> n"
  by (induct n) (auto)


(*contributed by Paulo Emílio de Vilhena*)
lemma (in ring_hom_ring) inj_on_domain:
  assumes "inj_on h (carrier R)"
  shows "domain S \<Longrightarrow> domain R"
proof -
  assume A: "domain S" show "domain R"
  proof
    have "h \<one> = \<one>\<^bsub>S\<^esub> \<and> h \<zero> = \<zero>\<^bsub>S\<^esub>" by simp
    hence "h \<one> \<noteq> h \<zero>"
      using domain.one_not_zero[OF A] by simp
    thus "\<one> \<noteq> \<zero>"
      using assms unfolding inj_on_def by fastforce 
  next
    fix a b
    assume a: "a \<in> carrier R"
       and b: "b \<in> carrier R"
    have "h (a \<otimes> b) = (h a) \<otimes>\<^bsub>S\<^esub> (h b)" by (simp add: a b)
    also have " ... = (h b) \<otimes>\<^bsub>S\<^esub> (h a)" using a b A cringE(1)[of S]
      by (simp add: cring.cring_simprules(14) domain_def)
    also have " ... = h (b \<otimes> a)" by (simp add: a b)
    finally have "h (a \<otimes> b) = h (b \<otimes> a)" .
    thus "a \<otimes> b = b \<otimes> a"
      using assms a b unfolding inj_on_def by simp 
    
    assume  ab: "a \<otimes> b = \<zero>"
    hence "h (a \<otimes> b) = \<zero>\<^bsub>S\<^esub>" by simp
    hence "(h a) \<otimes>\<^bsub>S\<^esub> (h b) = \<zero>\<^bsub>S\<^esub>" using a b by simp
    hence "h a =  \<zero>\<^bsub>S\<^esub> \<or> h b =  \<zero>\<^bsub>S\<^esub>" using a b domain.integral[OF A] by simp
    thus "a = \<zero> \<or> b = \<zero>"
      using a b assms unfolding inj_on_def by force
  qed
qed

end
