(* Title: Bruck_Ryser_Chowla
   Author: Craig Alan Feinstein
*)

theory Bruck_Ryser_Chowla imports
  Fishers_Inequality.Fishers_Inequality SumSquares.FourSquares Pell.Pell 
  Van_der_Waerden.Digits
begin 

section ‹Bruck Ryser Chowla Theorem›
text ‹The Bruck Ryser Chowla Theorem states the following:
Let $(v,k,\Lambda)$ be a symmetric BIBD. If v is even, 
then $k-\Lambda$ will be a perfect square. And if v is odd,
then there will exist integers $(x,y,z) \neq (0,0,0)$ such that
$x^2 = (k-Λ) y^2 = (-1)^{(v-1)/2}Λz^2$. The proof comes from 
"Combinatorial Designs: Constructions and Analysis" by Douglas R.
Stinson.›

context ordered_sym_bibd
begin

subsection ‹v is even›

lemma apply_nec_cond_one_1: shows "𝗄 * (𝗄 - 1) = Λ * (𝗏 - 1)"
proof -
  have "𝗋 = 𝗄" using rep_value_sym by simp
    moreover have "𝗋 * (𝗄 - 1) = Λ * (𝗏 - 1)"
     using necessary_condition_one by simp
      ultimately show "𝗄 * (𝗄 - 1) = Λ * (𝗏 - 1)" by simp
    qed

lemma apply_nec_cond_one_2: shows "𝗄 + Λ * (𝗏 - 1) = 𝗄^2"
proof -
  have "𝗄 + Λ * (𝗏 - 1) = 𝗄 + 𝗄 * (𝗄 - 1)"
    using apply_nec_cond_one_1 by simp
    also have "𝗄 + 𝗄 * (𝗄 - 1) = 𝗄^2"
      by (simp add: algebra_simps power2_eq_square)
    ultimately show "𝗄 + Λ * (𝗏 - 1) = 𝗄^2"
      using apply_nec_cond_one_1 by simp
  qed

lemma apply_nec_cond_one_3: shows
  "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
proof -
  have "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
    using apply_nec_cond_one_2 by simp
  thus ?thesis by simp
qed

lemma det_incidence: "(det N)^2 = det (N * N⇧T)"
proof - 
  have "det (N * N⇧T) = det N * det N⇧T" 
  by (metis (full_types) N_carrier_mat det_mult local.symmetric transpose_carrier_mat)
  also have "det N * det N⇧T = det N * det N"
  using N_carrier_mat det_transpose local.symmetric by auto
  then have "det (N * N⇧T) = (det N)^2" by (simp add: calculation power2_eq_square)
  thus ?thesis by simp
qed 

lemma sym_det_in_mat_square:
 "(det N)^2 = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
proof - 
  have "det (N * N⇧T) = (𝗋 + Λ * (𝗏 - 1))* (𝗋 - Λ)^(𝗏 - 1)"
    using determinant_inc_mat_square by simp
    then have "det (N * N⇧T) = (𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1)"
      using rep_value_sym by simp
    also have "(𝗄 + Λ * (𝗏 - 1))* (𝗄 - Λ)^(𝗏 - 1) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)"
      using apply_nec_cond_one_3 by simp
    then have "det (N * N⇧T) = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" 
      using calculation by argo
    then show ?thesis using det_incidence by simp
  qed

lemma power_of_k_minus_lambda_1:
  "(det N)^2 / 𝗄^2 = (𝗄 - Λ)^(𝗏 - 1)" 
proof - 
  have "(det N)^2 = 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" 
    using sym_det_in_mat_square by simp
  then have "(det N)^2 / 𝗄^2 = (𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)) / 𝗄^2" 
    by (simp add: divide_simps)
  also have "... = 𝗄^2 / 𝗄^2 * (𝗄 - Λ)^(𝗏 - 1)" by (simp add: divide_simps)
  also have "... = 1 * (𝗄 - Λ)^(𝗏 - 1)" using rep_not_zero by fastforce
  also have "... = (𝗄 - Λ)^(𝗏 - 1)" by auto
  finally show ?thesis .
  qed

lemma power_of_k_minus_lambda_2: 
  "(det N / 𝗄)^2 = (𝗄 - Λ)^(𝗏 - 1)"
proof -
  have "(det N)^2 / 𝗄^2 = (𝗄 - Λ)^(𝗏 - 1)" 
    using power_of_k_minus_lambda_1 by simp
  then show ?thesis by (simp add: power_divide)
qed

lemma power_of_k_minus_lambda_3: "(sqrt(𝗄 - Λ))^(𝗏 - 1) ∈ ℚ"
proof -
  have "(det N / 𝗄)^2 = (𝗄 - Λ)^(𝗏 - 1)"
    using power_of_k_minus_lambda_2 by simp
  then have "sqrt((𝗄 - Λ)^(𝗏 - 1)) = sqrt((det N / 𝗄)^2)" by auto
  then have "sqrt((𝗄 - Λ)^(𝗏 - 1)) = abs(det N / 𝗄)"
    by (metis real_sqrt_abs)
  also have "(sqrt(𝗄 - Λ))^(𝗏 - 1) = sqrt ((𝗄 - Λ)^(𝗏 - 1))"
      by (simp add: real_sqrt_power) 
  then have "(sqrt(𝗄 - Λ))^(𝗏 - 1) = abs(det N / 𝗄)"
      using calculation by presburger
  also have "abs(det N / 𝗄) ∈ ℚ" by simp
  then show ?thesis by (metis (full_types)
        ‹sqrt (real (𝗄 - Λ)) ^ (𝗏 - 1) = ¦real_of_int (det N) / real 𝗄¦›)
qed

lemma blocksize_gt_index: "𝗄 > Λ"
  using rep_value_sym index_lt_replication by auto

lemma bruck_ryser_chowla_even_rat:
  assumes "even 𝗏"
  shows "sqrt(𝗄 - Λ) ∈ ℚ"
proof -
  have diff_rat: ‹𝗄 - Λ ∈ ℚ› by simp
  have eq: "(sqrt(𝗄 - Λ))^(𝗏 - 1) ∈ ℚ" using power_of_k_minus_lambda_3
    by blast
  from assms obtain m where "𝗏 = 2 * m" "m > 0" using v_non_zero by auto
  then have "𝗏 - 1 = 2 * m - 1" by auto
  then have "(sqrt(𝗄 - Λ))^(2 * m - 1) ∈ ℚ"
    using eq by auto
  then have rat: ‹(sqrt(𝗄 - Λ))^(2 * m) / (sqrt(𝗄 - Λ)) ∈ ℚ›
    using ‹0 < m› div_by_0 div_less_iff_less_mult mult.commute
        nonzero_mult_div_cancel_left one_div_two_eq_zero pos2 power_eq_0_iff
        power_minus_mult zero_less_diff
    by (metis nat_0_less_mult_iff) 
  have eq2: ‹(sqrt(𝗄 - Λ))^(2 * m) / (sqrt(𝗄 - Λ)) = 
    ((𝗄 - Λ))^ m * (1/sqrt(𝗄 - Λ))›
    using blocksize_gt_index
    by (simp add: power_mult)
  moreover have ‹(𝗄 - Λ) ^ m ∈ ℚ›
    using diff_rat by (simp add: power_mult Rats_mult_iff)
  ultimately have ‹1/sqrt(𝗄 - Λ) ∈ ℚ›
    using rat blocksize_gt_index Rats_mult_iff by force
  then show ?thesis
    by (simp add: divide_inverse)
qed

theorem bruck_ryser_chowla_even:
  assumes "even 𝗏"
  shows "sqrt(𝗄 - Λ) ∈ ℕ"
proof -
  have brc_rat: "sqrt(𝗄 - Λ) ∈ ℚ" 
    using bruck_ryser_chowla_even_rat assms by simp
  then show ?thesis using sqrt_nat_or_irrat' by blast  
qed

end

subsection ‹v is odd›

sublocale ordered_bibd ⊆ ordered_regular_pairwise_balance 𝒱s ℬs Λ 𝗋
  by unfold_locales

context ordered_sym_bibd
begin

lemma lambda_all_ones_extension:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. ∑h ∈ {0..<𝗏}.
      (of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))
   = of_nat Λ * (∑j ∈ {0..<𝗏}. x $$ (j, 0))^2"
proof -
  have J: "(of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j,h) = of_nat Λ"
    if "j < 𝗏" "h < 𝗏" for j h
    using that by simp
  have "(∑j ∈ {0..<𝗏}. ∑h ∈ {0..<𝗏}. (of_nat Λ ⋅⇩m J⇩m 𝗏) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))
    = (∑j=0..<𝗏. ∑h=0..<𝗏. of_nat Λ * x$$(j,0) * x$$(h,0))"
    using J by simp
  also have "... = (∑j=0..<𝗏. ∑h=0..<𝗏. of_nat Λ * (x$$(j,0) * x$$(h,0)))"
    by (simp add: algebra_simps)
  also have "… = (∑j ∈ {0..<𝗏}. of_nat Λ * (∑h ∈ {0..<𝗏}. x$$(j,0) * x$$(h,0)))"
    by (simp add: sum_distrib_left)
  also have "… = of_nat Λ * (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. x$$(j,0) * x$$(h,0)))"
    by (simp add: sum_distrib_left)
  also have "… = of_nat Λ * ((∑j ∈ {0..<𝗏}. x$$(j,0)) * (∑h ∈ {0..<𝗏}. x$$(h,0)))"
    by (metis sum_product)
  also have "… = of_nat Λ * (∑j ∈ {0..<𝗏}. x$$(j,0))^2"
    by (metis power2_eq_square)
  finally show ?thesis .
qed

lemma order_times_identity_matrix:
  fixes x :: "rat mat"
  shows
  "(∑ j<𝗏. ∑ h<𝗏.
      (rat_of_nat (𝗋 - Λ) ⋅⇩m 1⇩m 𝗏) $$ (j,h) * x $$ (j,0) * x $$ (h,0))
   = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. (x $$ (j,0))^2)"
proof -
  have step: "⋀j h. rat_of_nat (𝗋 - Λ) * (if j = h then 1 else 0) * x $$ (j,0) * x $$ (h,0) =
                     (if j = h then rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (h,0) else 0)"
    by auto
  have "(∑ j<𝗏. ∑ h<𝗏. (rat_of_nat (𝗋 - Λ) ⋅⇩m 1⇩m 𝗏) $$ (j,h) * x $$ (j,0) * x $$ (h,0))
      = (∑ j<𝗏. ∑ h<𝗏. rat_of_nat (𝗋 - Λ) * (if j = h then 1 else 0) * x $$ (j,0) * x $$ (h,0))"
    unfolding one_mat_def by simp
  also have "... = (∑ j<𝗏. ∑ h<𝗏. (if j = h then rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (h,0) else 0))"
    by (subst step) simp
  also have "... = (∑ j<𝗏. rat_of_nat (𝗋 - Λ) * x $$ (j,0) * x $$ (j,0))"
    by simp
  also have "... = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. x $$ (j,0) * x $$ (j,0))"
    by (simp add: sum_distrib_left mult.assoc)
  also have "... = rat_of_nat (𝗋 - Λ) * (∑ j<𝗏. (x $$ (j,0))^2)"
    unfolding power2_eq_square by simp
  finally show ?thesis .
qed

lemma combine_r_lambda_terms:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (∑j ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0))) = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 + 
    of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have lam: "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏} .(of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
    of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2"
  proof -
    have "(of_int (int Λ) ⋅⇩m (J⇩m 𝗏 :: rat mat)) = (of_nat Λ ⋅⇩m (J⇩m 𝗏 :: rat mat))"
      by simp
    then show ?thesis using lambda_all_ones_extension by fastforce
  qed
  have ord: "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
        of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
  proof -
    have eq: "(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏 :: rat mat)) = (rat_of_nat (𝗋 - Λ) ⋅⇩m (1⇩m 𝗏 :: rat mat))"
      by simp
    have "(∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
          (∑j ∈{0..<𝗏} .(∑h ∈{0..<𝗏}.(rat_of_nat (𝗋 - Λ) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))"
      using eq by metis
    also have "... = rat_of_nat (𝗋 - Λ) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
      using order_times_identity_matrix[of x] by (simp add: atLeast0LessThan)
    also have "... = of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis using lam ord by simp
qed

lemma brc_x_identity:
  fixes x :: "rat mat"
  shows "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0))) =
     of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have matdef: "(∑i ∈{0..<𝗏} . 
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = of_int ((N * N⇧T) $$ (j, h))" 
    if "h < 𝗏" "j < 𝗏" for h j
    using transpose_mat_mult_entries[of "j" "N" "h"]
    local.symmetric that by simp
  have matcond: "of_int ((N * N⇧T) $$ (j, h)) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
    if "h < 𝗏" "j < 𝗏" for h j 
    using rpbd_incidence_matrix_cond that(1) that(2) by simp
  have sum_eq_rLambda: "(∑i ∈ {0..<𝗏}. of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
    if "h < 𝗏" "j < 𝗏" for h j
  proof -
    have "(∑i ∈{0..<𝗏} . of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = of_int ((N * N⇧T) $$ (j, h))"
      using matdef[OF that] .
    also have "... = ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) :: rat)"
      using matcond[OF that] .
    finally show ?thesis .
  qed
  have "(∑i ∈ {0..<𝗏}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0) = 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h)) * 
    x $$ (j, 0) * x $$ (h, 0)" if "h < 𝗏" "j < 𝗏" for h j
    using sum_eq_rLambda[OF that] by simp
  then have "(∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0))) = 
    (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏) + of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h)) *
     x $$ (j, 0) * x $$ (h, 0)))" by (intro sum.mono_neutral_cong_right) auto
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)) +
    (of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) +
    (∑h ∈ {0..<𝗏}.(of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" by (simp add: sum.distrib)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. 
    ((of_int (int Λ) ⋅⇩m (J⇩m 𝗏)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (∑j ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. (of_int (int (𝗋 - Λ)) ⋅⇩m (1⇩m 𝗏)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" 
    by (simp add: sum.distrib)
  also have final_equ:  "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 + 
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using combine_r_lambda_terms by simp
  finally show ?thesis .
qed

lemma brc_x_equation:
  fixes x :: "rat mat"
  shows "(∑i ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
     of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
proof -
  have r_eq_k: "𝗋 = 𝗄" using rep_value_sym by simp
  have "(∑i ∈ {0..<𝗏}.(∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
    (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. of_int (N $$ (j, i)) *
    x $$ (j, 0)) * (∑h ∈ {0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h, 0)))"
    by (simp add: power2_eq_square)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    (of_int (N $$ (j, i)) * x $$ (j,0)) * (of_int (N $$ (h,i)) * x $$ (h,0)))))"
    by (metis (no_types) sum_product)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * (x $$ (j,0) * of_int (N $$ (h,i))) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * (of_int (N $$ (h,i)) * x $$ (j,0)) * x $$ (h,0))))"
    by (metis (no_types, lifting) mult_of_int_commute sum.cong)
  also have "... = (∑i ∈ {0..<𝗏}. (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}.
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    using sum_reorder_triple[of "λ i j h . of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * 
        x $$ (j,0) * x $$ (h,0)" "{0..<𝗏}" "{0..<𝗏}" "{0..<𝗏}"] 
    by blast
  also have "... = (∑j ∈ {0..<𝗏}. (∑h ∈ {0..<𝗏}. (∑i ∈ {0..<𝗏}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}.(x $$ (j, 0)))^2 +
     of_int (int (𝗋 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using brc_x_identity by simp
  also have "... = of_int (int Λ) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0)))^2 +
     of_int (int (𝗄 - Λ)) * (∑j ∈ {0..<𝗏}. (x $$ (j, 0))^2)"
    using r_eq_k by simp
  finally show ?thesis .
qed

fun y_reversible :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
             ((nat × nat × nat × nat) × (rat × rat × rat × rat))" where
  "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = ((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))"

fun y_of :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
                  (rat × rat × rat × rat)" where
  "y_of((a, b, c, d),(x0, x1, x2, x3)) = snd(y_reversible((a, b, c, d),(x0, x1, x2, x3)))"

fun y_inv_reversible ::"((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
             ((nat × nat × nat × nat) × (rat × rat × rat × rat))" where
  "y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)) = ((a, b, c, d),
  ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
  ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))"

fun y_inv_of :: "((nat × nat × nat × nat) × (rat × rat × rat × rat)) ⇒ 
                  (rat × rat × rat × rat)" where
  "y_inv_of((a, b, c, d),(y0, y1, y2, y3)) = 
   snd(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"

fun one_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "one_of(y0, y1, y2, y3) = y0"

fun two_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "two_of(y0, y1, y2, y3) = y1"

fun three_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "three_of(y0, y1, y2, y3) = y2"

fun four_of :: "(rat × rat × rat × rat) ⇒ rat" where
  "four_of(y0, y1, y2, y3) = y3"

lemma y_inverses_part_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  assumes "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))"
proof - 
  have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = ((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))" by simp
  then have "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
   y_inv_reversible((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))" by simp
  then have key: "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
   ((a, b, c, d),
   ((of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) - 
    of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) - 
    of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) - 
    of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) + 
    of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) + 
    of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) - 
    of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
    of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
    of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
    of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2),
    (of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
    of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
    of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
    of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3))/
    of_nat(a^2 + b^2 + c^2 + d^2)))"
    by simp

  have "of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
    of_nat(a^2 + b^2 + c^2 + d^2) * x0"
    by (simp add: power2_eq_square algebra_simps)

  then have
     "(of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = x0 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
    of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have first_component_simplified: 
     "(of_nat a * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat b * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat c * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat d * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = x0"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
    of_nat(a^2 + b^2 + c^2 + d^2) *x1"
    by (simp add: power2_eq_square algebra_simps)

  then have
    "(of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x1 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have second_component_simplified:
    "(of_nat b * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat a * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat d * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) -
     of_nat c * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x1"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * x2"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x2 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have third_component_simplified:
    "(of_nat c * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) -
     of_nat d * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) +
     of_nat a * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat b * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x2"
    using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  have "of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * x3"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x3 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have fourth_component_simplified:
    "(of_nat d * (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3) +
     of_nat c * (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3) -
     of_nat b * (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3) +
     of_nat a * (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = x3"
   using assms by (metis nonzero_eq_divide_eq of_nat_0_eq_iff)

  then have "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))"
  using first_component_simplified second_component_simplified 
       third_component_simplified fourth_component_simplified key by simp
  thus ?thesis 
    by simp
qed

lemma y_inverses_part_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  assumes "a^2 + b^2 + c^2 + d^2 ≠ 0"
  shows "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
         ((a, b, c, d),(y0, y1, y2, y3))"
proof - 
  have "y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)) = ((a, b, c, d),
   ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
   ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))" 
      by simp
  then have "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
   y_reversible((a, b, c, d),
   ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
   ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
   ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))" 
    by simp
  then have key: "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
   ((a, b, c, d),
   (of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) - 
    of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) + 
    of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) -
    of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2),
    -of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) -
    of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/
    of_nat(a^2 + b^2 + c^2 + d^2) +
    of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/
    of_nat(a^2 + b^2 + c^2 + d^2)))"
    by auto

  have "of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
    of_nat(a^2 + b^2 + c^2 + d^2) * y0"
    by (simp add: power2_eq_square algebra_simps)

  then have
     "(of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y0 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have first_component_simplified: 
     "of_nat a * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat b * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat c * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat d * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
    of_nat(a^2 + b^2 + c^2 + d^2) = y0"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
    of_nat(a^2 + b^2 + c^2 + d^2) *y1"
    by (simp add: power2_eq_square algebra_simps)

  then have
    "(-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y1 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have second_component_simplified:
    "-of_nat b * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat d * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat c * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y1"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) + 
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * y2"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) +
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y2 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have third_component_simplified:
    "-of_nat c * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat d * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat b * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y2"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  have "-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) = 
     of_nat(a^2 + b^2 + c^2 + d^2) * y3"
    by (simp add: power2_eq_square algebra_simps)

  then have 
    "(-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y3 * of_nat(a^2 + b^2 + c^2 + d^2)/ 
     of_nat(a^2 + b^2 + c^2 + d^2)"
    using assms by (simp add: algebra_simps)

  then have fourth_component_simplified:
    "-of_nat d * ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) -
     of_nat c * ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat b * ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1) / 
     of_nat(a^2 + b^2 + c^2 + d^2) +
     of_nat a * ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2) / 
     of_nat(a^2 + b^2 + c^2 + d^2) = y3"
   using assms by (smt (verit, best) add_divide_distrib diff_divide_distrib
      nonzero_eq_divide_eq of_nat_0 of_nat_0_eq_iff)

  then have "y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))) = 
         ((a, b, c, d),(y0, y1, y2, y3))"
  using first_component_simplified second_component_simplified 
       third_component_simplified fourth_component_simplified key by auto
  thus ?thesis 
    by simp
qed

lemma lagrange_trans_of_4_identity:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  shows "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
         two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
         three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
         four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
         of_nat (a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2)"
proof -
  have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
    ((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0  -(of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2" by auto

  have eq1: "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 = 
        (of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2 +
        2*(of_nat a)*(of_nat b)*x0*x1 + 2*(of_nat a)*(of_nat c)*x0*x2 + 
        2*(of_nat a)*(of_nat d)*x0*x3 + 2*(of_nat b)*(of_nat c)*x1*x2 + 
        2*(of_nat b)*(of_nat d)*x1*x3 + 2*(of_nat c)*(of_nat d)*x2*x3"
    by (simp add: power2_eq_square algebra_simps)

  have eq2: "(-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 = 
        (of_nat a^2)*x1^2 + (of_nat b^2)*x0^2 + (of_nat c^2)*x3^2 + 
        (of_nat d^2)*x2^2 - 2*(of_nat a)*(of_nat b)*x0*x1 + 
        2*(of_nat a)*(of_nat c)*x1*x3 - 2*(of_nat a)*(of_nat d)*x1*x2 - 
        2*(of_nat b)*(of_nat c)*x0*x3 + 2*(of_nat b)*(of_nat d)*x0*x2 - 
        2*(of_nat c)*(of_nat d)*x2*x3"
    by (simp add: power2_eq_square algebra_simps)

  have eq3: "(-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 = 
       (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2 + (of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 - 
       2*(of_nat a)*(of_nat b)*x2*x3 - 2*(of_nat a)*(of_nat c)*x0*x2 + 
       2*(of_nat a)*(of_nat d)*x1*x2 + 2*(of_nat b)*(of_nat c)*x0*x3 - 
       2*(of_nat b)*(of_nat d)*x1*x3 - 2*(of_nat c)*(of_nat d)*x0*x1"
    by (simp add: power2_eq_square algebra_simps)

  have eq4: "(-(of_nat d)*x0 - (of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
       (of_nat a^2)*x3^2 + (of_nat b^2)*x2^2 + (of_nat c^2)*x1^2 + (of_nat d^2)*x0^2 +
       2*(of_nat a)*(of_nat b)*x2*x3 - 2*(of_nat a)*(of_nat c)*x1*x3 - 
       2*(of_nat a)*(of_nat d)*x0*x3 - 2*(of_nat b)*(of_nat c)*x1*x2 - 
       2*(of_nat b)*(of_nat d)*x0*x2 + 2*(of_nat c)*(of_nat d)*x0*x1"
    by (simp add: power2_eq_square algebra_simps)

  (* Combine all the results *)
  have eq5: "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0 - (of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
    ((of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2) + 
    ((of_nat b^2)*x0^2 + (of_nat a^2)*x1^2 + (of_nat d^2)*x2^2 + (of_nat c^2)*x3^2) + 
    ((of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 + (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2) + 
    ((of_nat d^2)*x0^2 + (of_nat c^2)*x1^2 + (of_nat b^2)*x2^2 + (of_nat a^2)*x3^2)"
    using eq1 eq2 eq3 eq4 by (simp add: algebra_simps)

  have "of_nat(a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2) =
    ((of_nat a^2)*x0^2 + (of_nat b^2)*x1^2 + (of_nat c^2)*x2^2 + (of_nat d^2)*x3^2) + 
    ((of_nat b^2)*x0^2 + (of_nat a^2)*x1^2 + (of_nat d^2)*x2^2 + (of_nat c^2)*x3^2) + 
    ((of_nat c^2)*x0^2 + (of_nat d^2)*x1^2 + (of_nat a^2)*x2^2 + (of_nat b^2)*x3^2) + 
    ((of_nat d^2)*x0^2 + (of_nat c^2)*x1^2 + (of_nat b^2)*x2^2 + (of_nat a^2)*x3^2)" 
    by (simp add: algebra_simps)

  then have "((of_nat a)*x0 + (of_nat b)*x1 + (of_nat c)*x2 + (of_nat d)*x3)^2 +
    (-(of_nat b)*x0 + (of_nat a)*x1 - (of_nat d)*x2 + (of_nat c)*x3)^2 +
    (-(of_nat c)*x0 + (of_nat d)*x1 + (of_nat a)*x2 - (of_nat b)*x3)^2 +
    (-(of_nat d)*x0  -(of_nat c)*x1 + (of_nat b)*x2 + (of_nat a)*x3)^2 = 
    of_nat(a^2 + b^2 + c^2 + d^2)*(x0^2 + x1^2 + x2^2 + x3^2)"
    using eq5 by (simp add: add.commute add.left_commute)

  thus ?thesis
    by simp
qed

definition sum4sq_nat :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat" where
  "sum4sq_nat a b c d = a^2 + b^2 + c^2 + d^2"

definition is_sum4sq_nat :: "nat ⇒ bool" where
  "is_sum4sq_nat n ⟷ (∃a b c d :: nat. n = sum4sq_nat a b c d)"

lemma brc_v_odd_core:
  assumes v_odd: "odd 𝗏"
  assumes four_sq_int:
    "A^2 + B^2 + C^2 + D^2 = int (𝗄 - Λ)"
  shows "∃x y z :: int.
           (x, y, z) ≠ (0, 0, 0) ∧
           x^2 = int (𝗄 - Λ) * y^2 +
                 ((-1) ^ ((𝗏 - 1) div 2)) * int Λ * z^2"
  sorry

lemma bruck_ryser_chowla_odd:
  assumes v_odd: "odd 𝗏"
  shows "∃x y z :: int.
           (x, y, z) ≠ (0, 0, 0) ∧
           x^2 = int (𝗄 - Λ) * y^2 +
                 ((-1) ^ ((𝗏 - 1) div 2)) * int Λ * z^2"
proof -
  ― ‹Step 1: matrix identity N * Nᵀ = Λ Jᵥ + (k - Λ) Iᵥ›
  have NNt_decomp:
    "N * N⇧T = Λ ⋅⇩m J⇩m 𝗏 + (𝗄 - Λ) ⋅⇩m 1⇩m 𝗏"
  proof -
    from rpbd_incidence_matrix_cond
    have "N * N⇧T = Λ ⋅⇩m J⇩m 𝗏 + (𝗋 - Λ) ⋅⇩m 1⇩m 𝗏" .
    moreover have "𝗋 = 𝗄"
      using rep_value_sym by simp
    ultimately show ?thesis by simp
  qed

  ― ‹Step 2: determinants; det(N * Nᵀ) is a square›
  have det_square:
    "det (Λ ⋅⇩m J⇩m 𝗏 + (𝗄 - Λ) ⋅⇩m 1⇩m 𝗏) = (det N)^2"
  proof -
    have "det (Λ ⋅⇩m J⇩m 𝗏 + (𝗄 - Λ) ⋅⇩m 1⇩m 𝗏) = det (N * N⇧T)"
      using NNt_decomp by simp
    also have "... = (det N)^2"
      using det_incidence by simp
    finally show ?thesis .
  qed

  ― ‹Step 3: closed form for det(Λ Jᵥ + (k−Λ) Iᵥ)›
  have det_JI:
    "det (Λ ⋅⇩m J⇩m 𝗏 + (𝗄 - Λ) ⋅⇩m 1⇩m 𝗏)
       = (𝗄 + Λ * (𝗏 - 1)) * (𝗄 - Λ) ^ (𝗏 - 1)"
  proof -
    have "det (N * N⇧T) = (𝗋 + Λ * (𝗏 - 1)) * (𝗋 - Λ) ^ (𝗏 - 1)"
      using determinant_inc_mat_square by simp
    also have "... = (𝗄 + Λ * (𝗏 - 1)) * (𝗄 - Λ) ^ (𝗏 - 1)"
      using rep_value_sym by simp
    finally show ?thesis
      using NNt_decomp by simp
  qed

  ― ‹Step 4: combine with det_square (currently unused, but mathematically important)›
  have det_closed:
    "(𝗄 + Λ * (𝗏 - 1)) * (𝗄 - Λ) ^ (𝗏 - 1) = (det N)^2"
    using det_JI det_square by simp

  ― ‹Use Lagrange’s four–square theorem from AFP to get k − Λ as sum of 4 squares›
  have ex4_nat: "∃a b c d :: nat. 𝗄 - Λ = a^2 + b^2 + c^2 + d^2" 
  proof - have "is_sum4sq_nat (𝗄 - Λ)" 
      unfolding is_sum4sq_nat_def sum4sq_nat_def 
      using FourSquares.sum_of_four_squares[of "𝗄 - Λ"] by simp 
    then show ?thesis unfolding is_sum4sq_nat_def sum4sq_nat_def by blast 
  qed 
  
  from ex4_nat obtain a b c d :: nat 
    where four_sq_nat: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2" 
    by blast

  ― ‹Convert to an integer equation A² + B² + C² + D² = int (k − Λ)›
  define A :: int where "A = int a"
  define B :: int where "B = int b"
  define C :: int where "C = int c"
  define D :: int where "D = int d"

  have four_sq_int:
    "A^2 + B^2 + C^2 + D^2 = int (𝗄 - Λ)"
  proof -
    have "int (𝗄 - Λ) = int (a^2 + b^2 + c^2 + d^2)"
      using four_sq_nat by simp
    also have "... = (int a)^2 + (int b)^2 + (int c)^2 + (int d)^2"
      by simp
    also have "... = A^2 + B^2 + C^2 + D^2"
      unfolding A_def B_def C_def D_def by simp
    finally show ?thesis by simp
  qed

  ― ‹Step 5: plug everything into the number-theoretic core lemma›
  have ex_xyz:
    "∃x y z :: int.
       (x, y, z) ≠ (0, 0, 0) ∧
       x^2 = int (𝗄 - Λ) * y^2 +
             ((-1) ^ ((𝗏 - 1) div 2)) * int Λ * z^2"
    using brc_v_odd_core[OF v_odd four_sq_int] .

  from ex_xyz show ?thesis
    by blast
qed

end
