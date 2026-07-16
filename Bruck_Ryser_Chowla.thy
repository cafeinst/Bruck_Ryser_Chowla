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

lemma linear_comb_of_y_part_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
           "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"       
  shows "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  have key: "y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3))) = 
         ((a, b, c, d),(x0, x1, x2, x3))" 
  using y_inverses_part_1 assms(1) blocksize_gt_index 
  by (metis less_numeral_extra(3) zero_less_diff)

  let ?D = "of_nat (a^2 + b^2 + c^2 + d^2) :: rat"
  let ?y0 = "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
  let ?y1 = "two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y2 = "three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?y3 = "four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
  let ?e0 = "of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
             of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D"
  let ?e1 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
              of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D"
  let ?e2 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D"
  let ?e3 = "-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
              of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D"

  have oneof: "x0 = 
    one_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x0 = ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D"
    by simp
  then have first_1: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) *
    ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have first_2: "of_int(N $$ (m-4,m-i-1)) * ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - 
    (of_nat d)*?y3)/?D = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  then have first: "of_int(N $$ (m-4,m-i-1)) * x0 = of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D" 
    using first_1 first_2 by argo

  have twoof: "x1 = 
    two_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x1 = ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D"
    by simp
  then have second_1: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) *
    ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have second_2: "of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - 
    (of_nat c)*?y3)/?D = of_int(N $$ (m-3,m-i-1)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have second_3: "of_int(N $$ (m-3,m-i-1)) *((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D = (of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have second_4: "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D = 
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + 
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D" 
    by presburger
  then have second: "of_int(N $$ (m-3,m-i-1)) * x1 = of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
     of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - 
     of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D"
    using second_1 second_2 second_3 second_4 by argo

  have threeof: "x2 = 
    three_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x2 = ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D"
    by simp
  then have third_1: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) *
    ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have third_2: "of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - 
    (of_nat d)*?y1)/?D = of_int(N $$ (m-2,m-i-1)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3)/?D - 
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have third_3: "of_int(N $$ (m-2,m-i-1)) *((of_nat c)*?y0 + (of_nat a)*?y2 + 
    (of_nat b)*?y3)/?D = (of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have third_4: "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3)/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D = 
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D" 
    by presburger
  then have third: "of_int(N $$ (m-2,m-i-1)) * x2 = of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D - 
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D"
    using third_1 third_2 third_3 third_4 by argo

  have fourof: "x3 = 
    four_of(snd(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x3 = ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D"
    by simp
  then have fourth_1: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) *
    ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have fourth_2: "of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - 
    (of_nat b)*?y2)/?D = of_int(N $$ (m-1,m-i-1)) * ((of_nat d)*?y0 + (of_nat c)*?y1 +
    (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have fourth_3: "of_int(N $$ (m-1,m-i-1)) *((of_nat d)*?y0 + (of_nat c)*?y1 + 
    (of_nat a)*?y3)/?D = (of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have fourth_4: "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D = 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D" 
    by presburger
  then have fourth: "of_int(N $$ (m-1,m-i-1)) * x3 = of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D +
     of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D - 
     of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D"
    using fourth_1 fourth_2 fourth_3 fourth_4 by argo 

  have sum: "of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 + 
    of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 =
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D"
    using first second third fourth by linarith
  have sumdef: "(∑h ∈ {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x $$ (m-4,0) + of_int(N $$ (m-3,m-i-1)) * x $$ (m-3,0) + 
        of_int(N $$ (m-2,m-i-1)) * x $$ (m-2,0) + of_int(N $$ (m-1,m-i-1)) * x $$ (m-1,0)" 
    by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} ∪ {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} ∩ {4..<m}" by auto
  have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =
        (∑h ∈ {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) + 
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "λ h . 
    (of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 +
        of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using sumdef assms(4-8) by argo
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" using sum by argo
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D -
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    (of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D) * ?y0 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D) * ?y1 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D) * ?y2 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D) * ?y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    ?e00 * ?y0 + ?e01 * ?y1 + ?e02 * ?y2 + ?e03 * ?y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by blast
  then show ?thesis by blast
qed

lemma linear_comb_of_y_part_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = (𝗄 - Λ)"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"   
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  
  have "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     using linear_comb_of_y_part_1 assms(1-12) by fast
  then have "∃e0 e1 e2 e3 :: rat.(∑h ∈ {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    by simp

   then obtain e0 e1 e2 e3 where eq1:
    "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     by fast

  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms(9-12) by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
    using y_inverses_part_2 assms(1) assms(9-12) blocksize_gt_index 
    by (metis less_numeral_extra(3) zero_less_diff) 
  have eq3: "y0 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq4: "y1 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq5: "y2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have eq6: "y3 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))" 
    using eq2 by simp
  have "e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by (metis (no_types, lifting))
qed

lemma lagrange_identity_x:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
  shows "of_int(𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
         of_int(𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
         (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
proof -
  have eq0: "x0^2 = (x $$ (m-4,0))^2"
    using assms(5) by (simp add: of_rat_power)
  have eq1: "x1^2 = (x $$ (m-3,0))^2"
    using assms(6) by (simp add: of_rat_power)
  have eq2: "x2^2 = (x $$ (m-2,0))^2"
    using assms(7) by (simp add: of_rat_power)
  have eq3: "x3^2 = (x $$ (m-1,0))^2"
    using assms(8) by (simp add: of_rat_power)
  have eq: "x0^2 + x1^2 + x2^2 + x3^2 = 
    (x $$ (m-4,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-1,0))^2"
    using eq0 eq1 eq2 eq3 by (simp add: of_rat_add)
  have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (a^2 + b^2 + c^2 + d^2) * (x0^2 + x1^2 + x2^2 + x3^2)" 
    using lagrange_trans_of_4_identity[of a b c d x0 x1 x2 x3] assms(1-8) by blast
  then have "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)" using assms(1)
    by presburger
  then have keyform: "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_int(𝗄 - Λ) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 +
          (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)" using eq by simp
  have sumdef: "(∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) = (x $$ (m-1,0))^2 + 
        (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2" by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} ∪ {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} ∩ {4..<m}" by auto
  have "(∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        (∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) + 
        (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2)"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "λ j . (x $$ (m-j-1, 0))^2"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (𝗄 - Λ) * (∑j ∈ {0..<4}. (x $$ (m-j-1, 0))^2) + 
        of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2)" using algebra_simps by simp
  then have "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
        of_int (𝗄 - Λ) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)"
    using sumdef algebra_simps by auto
  then have "of_nat(𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_nat(𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
            (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
             two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using keyform algebra_simps by linarith
  thus ?thesis by simp
qed

lemma lagrange_identity_y:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes i :: "nat"
  fixes m :: "nat"
  assumes "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
          "𝗏 ≥ m" "m > 3" "i ∈ {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows   "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
           of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
           y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have eq1: "of_int (𝗄 - Λ) * (∑j ∈ {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_int (𝗄 - Λ) * (∑j ∈ {4..<m}. (x $$ (m-j-1, 0))^2) +
             (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
              two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
              four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using assms lagrange_identity_x by metis
  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
        using y_inverses_part_2 assms blocksize_gt_index 
        by (metis (no_types, lifting) neq0_conv zero_less_diff)
  have eq3: "y0^2 = one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq4: "y1^2 = two_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq5: "y2^2 = three_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have eq6: "y3^2 = four_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2" 
    using eq2 by simp
  have "y0^2 + y1^2 + y2^2 + y3^2 = 
        one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
        two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
        four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2"
    using eq3 eq4 eq5 eq6 by simp
  thus ?thesis using eq1 by simp
qed

lemma induction_step_0:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"        
        "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
         e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
         (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
        "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
        (e10 * y1 + e20 * y2 + e30 * y3 +
        (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  shows "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  have "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
               (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
   proof (cases "e00 = 1")
     case True   
    then have "y0 = -(e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y0 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using eq by simp
    then have "(-y0)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y0 = (e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00)"
      using assms(5) by auto
    then have "(1 - e00) * y0 = e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y0 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y0^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_1:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
            e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
           "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
           (e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  shows "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  have "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
   proof (cases "e11 = 1")
     case True   
    then have "y1 = -(e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y1 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using eq by simp
    then have "(-y1)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by auto
   next
    case False
    then have "y1 = (e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11)"
      using assms(5) by auto
    then have "(1 - e11) * y1 = e01 * y0 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y1 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y1^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_2:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
           e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
          "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
           (e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))" 
  shows "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  have "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
               (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
   proof (cases "e22 = 1")
     case True   
    then have "y2 = -(e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y2 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using eq by simp
    then have "(-y2)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y2 = (e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22)"
      using assms(5) by auto
    then have "(1 - e22) * y2 = e02 * y0 + e12 * y1 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y2 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y2^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_3:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x0 :: "rat"
  fixes x1 :: "rat"
  fixes x2 :: "rat"
  fixes x3 :: "rat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  fixes m :: "nat"
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(𝗄 - Λ)" "𝗏 ≥ m" "m > 3"
          "(∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
           e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
          "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
           (e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"
  shows "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have first_fact: "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
   proof (cases "e33 = 1")
     case True   
    then have "y3 = -(e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))  = 
          (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y3 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using eq by simp
    then have "(-y3)^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y3 = (e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33)"
      using assms(5) by auto
    then have "(1 - e33) * y3 = e03 * y0 + e13 * y1 + e23 * y2 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (∑h ∈ {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y3 = (∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y3^2 = ((∑h ∈ {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (∑h ∈ {m..<𝗏}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma induction_step_0_explicit:
  fixes e00 e10 e20 e30 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes y0_choice:
    "y0 =
      (if e00 = 1 then
        - (e10 * y1 + e20 * y2 + e30 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10 * y1 + e20 * y2 + e30 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e10 * y1 + e20 * y2 + e30 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))
     = e00 * y0 + ?A"
    using L0 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e00 = 1")
    case True
    then have y0_eq: "y0 = - ?A / 2"
      using y0_choice by simp

    have total_eq: "e00 * y0 + ?A = - y0"
      using True y0_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))
      = - y0"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y0_eq: "y0 = ?A / (1 - e00)"
      using y0_choice by simp
    then have "e00 * y0 + ?A = y0"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_1_explicit:
  fixes e01 e11 e21 e31 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes y1_choice:
    "y1 =
      (if e11 = 1 then
        - (e01 * y0 + e21 * y2 + e31 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01 * y0 + e21 * y2 + e31 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
  shows
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e01 * y0 + e21 * y2 + e31 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))
     = e11 * y1 + ?A"
    using L1 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e11 = 1")
    case True
    then have y1_eq: "y1 = - ?A / 2"
      using y1_choice by simp

    have total_eq: "e11 * y1 + ?A = - y1"
      using True y1_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))
      = - y1"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y1_eq: "y1 = ?A / (1 - e11)"
      using y1_choice by simp
    then have "e11 * y1 + ?A = y1"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_2_explicit:
  fixes e02 e12 e22 e32 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes y2_choice:
    "y2 =
      (if e22 = 1 then
        - (e02 * y0 + e12 * y1 + e32 * y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02 * y0 + e12 * y1 + e32 * y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
  shows
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e02 * y0 + e12 * y1 + e32 * y3 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))
     = e22 * y2 + ?A"
    using L2 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e22 = 1")
    case True
    then have y2_eq: "y2 = - ?A / 2"
      using y2_choice by simp

    have total_eq: "e22 * y2 + ?A = - y2"
      using True y2_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))
      = - y2"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y2_eq: "y2 = ?A / (1 - e22)"
      using y2_choice by simp
    then have "e22 * y2 + ?A = y2"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_3_explicit:
  fixes e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes y3_choice:
    "y3 =
      (if e33 = 1 then
        - (e03 * y0 + e13 * y1 + e23 * y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03 * y0 + e13 * y1 + e23 * y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  let ?A =
    "e03 * y0 + e13 * y1 + e23 * y2 +
     (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
     (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))"

  have Ltotal:
    "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))
     = e33 * y3 + ?A"
    using L3 by (simp add: algebra_simps)

  show ?thesis
  proof (cases "e33 = 1")
    case True
    then have y3_eq: "y3 = - ?A / 2"
      using y3_choice by simp

    have total_eq: "e33 * y3 + ?A = - y3"
      using True y3_eq
      by (simp add: field_simps)

    have "((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))
      = - y3"
      using Ltotal total_eq by simp

    then show ?thesis
      by simp
  next
    case False
    then have y3_eq: "y3 = ?A / (1 - e33)"
      using y3_choice by simp
    then have "e33 * y3 + ?A = y3"
      using False
      by (simp add: field_simps)
    then show ?thesis
      using Ltotal by simp
  qed
qed

lemma induction_step_0123_explicit:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes y0_choice:
    "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
  assumes y1_choice:
    "y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
  assumes y2_choice:
    "y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
  assumes y3_choice:
    "y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0_explicit[OF L0 y0_choice]
        induction_step_1_explicit[OF L1 y1_choice]
        induction_step_2_explicit[OF L2 y2_choice]
        induction_step_3_explicit[OF L3 y3_choice]
  by blast

lemma brc_v_eq_1:
  assumes v_eq_1: "𝗏 = 1"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows "∃x y z :: int. (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
         of_int(x^2) = of_nat(𝗄 - Λ) * of_int(y^2) + of_nat Λ * of_int(z^2)"
proof -
  (* For v=1, construct a simple x vector *)
  define x :: "rat mat" where "x = mat 1 1 (λ(i,j). 1)"
  
  have x_val: "x $$ (0, 0) = 1"
    using x_def by simp
  
  (* Apply brc_x_equation *)
  have brc_v1: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) =
                of_int Λ * (∑j ∈ {0..<1}. x $$ (j,0))^2 + 
                of_int(𝗄 - Λ) * (∑j ∈ {0..<1}. (x $$ (j,0))^2)"
    using brc_x_equation[of x] v_eq_1 by simp
  
  (* Simplify the LHS: sum over {0..<1} has only one term at index 0 *)
  have lhs_simpl: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) = 
                   (of_int(N $$ (0,0)) * x $$ (0,0))^2"
    by simp
  then have lhs_val: "(∑i ∈ {0..<1}. (∑h ∈ {0..<1}. of_int(N $$ (h,i)) * x $$ (h,0))^2) = 
                      (of_int(N $$ (0,0)))^2"
    using x_val by simp
  
  (* Simplify the RHS *)
  have sum_x: "(∑j ∈ {0..<1}. x $$ (j,0)) = x $$ (0,0)"
    by simp
  then have sum_x_val: "(∑j ∈ {0..<1}. x $$ (j,0)) = 1"
    using x_val by simp
  
  have sum_x2: "(∑j ∈ {0..<1}. (x $$ (j,0))^2) = (x $$ (0,0))^2"
    by simp
  then have sum_x2_val: "(∑j ∈ {0..<1}. (x $$ (j,0))^2) = 1"
    using x_val by simp
  
  (* Combine *)
  have n00_eq: "(of_int(N $$ (0,0)) :: rat)^2 = of_int Λ + of_int(𝗄 - Λ)"
    using brc_v1 lhs_val sum_x_val sum_x2_val by auto
  
  have kl_sum: "of_nat Λ + of_nat(𝗄 - Λ) = (of_nat 𝗄 :: rat)"
    using blocksize_gt_index of_nat_diff by simp

  then have "(of_int(N $$ (0,0)))^2 = (of_int 𝗄 :: rat)"
  using n00_eq by simp
  
  have "of_int((N $$ (0,0))^2) = of_nat(𝗄 - Λ) * of_int(1^2) + of_nat Λ * of_int(1^2)"
  proof -
    have "(of_int(N $$ (0,0)) :: rat)^2 = (of_nat(𝗄 - Λ) :: rat) + (of_nat Λ :: rat)"
      using n00_eq kl_sum by simp
    then have "of_int((N $$ (0,0))^2) = (of_nat(𝗄 - Λ) :: rat) + (of_nat Λ :: rat)"
      by (simp add: power2_eq_square)
    also have "... = of_nat(𝗄 - Λ) * 1 + of_nat Λ * 1"
      by simp
    finally show ?thesis
      by (metis (mono_tags, lifting) mult.right_neutral of_int_eq_iff of_int_hom.hom_one 
        of_int_of_nat_eq of_nat_add one_power2)
  qed

  moreover have "(N $$ (0,0) ≠ 0 ∨ (1::int) ≠ 0 ∨ (1::int) ≠ 0)"
    by simp

  ultimately show ?thesis by blast
qed

definition S_of :: "rat mat ⇒ rat" where
  "S_of x = (∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"

definition t_of :: "rat mat ⇒ rat" where
  "t_of x = (∑j∈{0..<𝗏}. x $$ (j,0))"

definition u_of :: "rat mat ⇒ rat" where
  "u_of x = (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"

lemma brc_recursive_elimination_weak:
  fixes x :: "rat mat"
  assumes brc_eq: "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
                 = of_int (int Λ) * (∑j∈{0..<𝗏}. x $$ (j,0))^2
                 + of_int (int (𝗄 - Λ)) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
  shows "∃S t u :: rat.
           S = of_int (int Λ) * t^2 + of_int (int (𝗄 - Λ)) * u ∧
           t = (∑j∈{0..<𝗏}. x $$ (j,0)) ∧
           u = (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
  using brc_eq by (intro exI[of _ "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"]
                   exI[of _ "(∑j∈{0..<𝗏}. x $$ (j,0))"]
                   exI[of _ "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)"]) simp

lemma brc_v_1_mod_4_identity:
  fixes a b c d m :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "x ≡ mat 𝗏 1 (λ(i,j).
    if j = 0 then
      (if i = m - 4 then x0
       else if i = m - 3 then x1
       else if i = m - 2 then x2
       else if i = m - 1 then x3
       else 0)
    else 0)"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)"
proof -
  have m4: "4 ≤ m"
    using m_props by simp

  let ?S = "{m - 4, m - 3, m - 2, m - 1}"

  have S_subset: "?S ⊆ {0..<𝗏}"
    using m_props m4 by auto

  have dists:
    "m - 4 ≠ m - 3"
    "m - 4 ≠ m - 2"
    "m - 4 ≠ m - 1"
    "m - 3 ≠ m - 2"
    "m - 3 ≠ m - 1"
    "m - 2 ≠ m - 1"
    using m4 by auto

  have xm4: "x $$ (m - 4,0) = x0"
    unfolding x_def using m_props m4 by simp

  have xm3: "x $$ (m - 3,0) = x1"
    unfolding x_def using m_props m4 by auto

  have xm2: "x $$ (m - 2,0) = x2"
    unfolding x_def using m_props m4 by auto

  have xm1: "x $$ (m - 1,0) = x3"
    unfolding x_def using m_props m4 by auto

  have outside_zero:
    "j ∈ {0..<𝗏} ⟹ j ∉ ?S ⟹ x $$ (j,0) = 0" for j
    unfolding x_def using m_props by auto

  have sum_all:
    "(∑j∈{0..<𝗏}. x $$ (j,0)) = x0 + x1 + x2 + x3"
  proof -
    have "(∑j∈{0..<𝗏}. x $$ (j,0)) = (∑j∈?S. x $$ (j,0))"
      by (rule sum.mono_neutral_cong_right) (use S_subset outside_zero in auto)
    also have "... = x0 + x1 + x2 + x3"
      using xm4 xm3 xm2 xm1 dists by simp
    finally show ?thesis .
  qed

  have sumsq_all:
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2) = x0^2 + x1^2 + x2^2 + x3^2"
  proof -
    have "(∑j∈{0..<𝗏}. (x $$ (j,0))^2) = (∑j∈?S. (x $$ (j,0))^2)"
      by (rule sum.mono_neutral_cong_right) (use S_subset outside_zero in auto)
    also have "... = x0^2 + x1^2 + x2^2 + x3^2"
      using xm4 xm3 xm2 xm1 dists by simp
    finally show ?thesis .
  qed

  show ?thesis
    using brc_x_equation[of x] sum_all sumsq_all
    by simp
qed

lemma y_of_norm:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  shows
   "let y = y_of ((a,b,c,d),(x0,x1,x2,x3)) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (a^2 + b^2 + c^2 + d^2) *
      (x0^2 + x1^2 + x2^2 + x3^2)"
  by (simp add: algebra_simps power2_eq_square)

lemma y_of_norm_brc:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows
   "let y = y_of ((a,b,c,d),(x0,x1,x2,x3)) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (𝗄 - Λ) *
      (x0^2 + x1^2 + x2^2 + x3^2)"
  using y_of_norm[of a b c d x0 x1 x2 x3] four_sq
  by simp

lemma brc_four_variable_substitution:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  defines "y ≡ y_of ((a,b,c,d),(x0,x1,x2,x3))"
  shows
   "of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2"
proof -
  have norm:
    "one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2
     =
     of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)"
    unfolding y_def
    using y_of_norm_brc[OF four_sq, of x0 x1 x2 x3]
    by simp
  show ?thesis
    using norm by simp
qed

lemma brc_v_1_mod_4_y_identity:
  fixes a b c d m :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "y ≡ y_of ((a,b,c,d),(x0,x1,x2,x3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + one_of y^2 + two_of y^2 + three_of y^2 + four_of y^2"
  using brc_v_1_mod_4_identity[OF four_sq m_props]
        brc_four_variable_substitution[OF four_sq, of x0 x1 x2 x3]
  unfolding y_def
  by simp

lemma brc_v_1_mod_4_y_identity_inv:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "xs ≡ y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have nz: "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using four_sq blocksize_gt_index by simp

  have yback:
    "y_of ((a,b,c,d), xs) = (y0,y1,y2,y3)"
    unfolding xs_def
    using y_inverses_part_2[OF nz, of y0 y1 y2 y3]
    by simp

  have norm:
    "of_nat (𝗄 - Λ) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
  proof -
    have norm0:
      "let y = y_of ((a,b,c,d),
          (one_of xs, two_of xs, three_of xs, four_of xs)) in
        one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
        =
        of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
      using y_of_norm_brc[OF four_sq,
        of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
      by simp

    have tuple_xs:
      "(one_of xs, two_of xs, three_of xs, four_of xs) = xs"
      by (cases xs) simp

    have norm1:
      "one_of (y_of ((a,b,c,d), xs))^2
      + two_of (y_of ((a,b,c,d), xs))^2
      + three_of (y_of ((a,b,c,d), xs))^2
      + four_of (y_of ((a,b,c,d), xs))^2
      =
      of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
      using norm0 tuple_xs
      by (simp add: Let_def)

    have "of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
      =
      one_of (y_of ((a,b,c,d), xs))^2
      + two_of (y_of ((a,b,c,d), xs))^2
      + three_of (y_of ((a,b,c,d), xs))^2
      + four_of (y_of ((a,b,c,d), xs))^2"
      using norm1 by simp

    also have "... = y0^2 + y1^2 + y2^2 + y3^2"
      using yback by simp

    finally show ?thesis .
  qed

  have base:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
    using brc_v_1_mod_4_identity[
      OF four_sq m_props,
      of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
    by simp

  show ?thesis
    using base norm by simp
qed

lemma brc_last_four_Li_linear_combinations:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0' y1' y2' y3' :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have i0_in: "(0::nat) ∈ {0..<4}" by simp
  have i1_in: "(1::nat) ∈ {0..<4}" by simp
  have i2_in: "(2::nat) ∈ {0..<4}" by simp
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  obtain c00 c10 c20 c30 where Li_m4:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
    c00*y0' + c10*y1' + c20*y2' + c30*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i3_in
          x0_def x1_def x2_def x3_def
          x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 3 - 1 = m - 4"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c01 c11 c21 c31 where Li_m3:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
    c01*y0' + c11*y1' + c21*y2' + c31*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i2_in
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 2 - 1 = m - 3"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c02 c12 c22 c32 where Li_m2:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
    c02*y0' + c12*y1' + c22*y2' + c32*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
      (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i1_in
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 1 - 1 = m - 2"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  obtain c03 c13 c23 c33 where Li_m1:
    "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
    c03*y0' + c13*y1' + c23*y2' + c33*y3' +
    (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0)) =
      e0 * y0' + e1 * y1' + e2 * y2' + e3 * y3' +
     (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
          OF four_sq m_v m_gt3 i0_in
          x0_def x1_def x2_def x3_def
          x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 0 - 1 = m - 1"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using Li_m4 Li_m3 Li_m2 Li_m1 by blast
qed

lemma brc_last_four_Ls_linear_combinations:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0' y1' y2' y3' :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0',y1',y2',y3')))"
  defines "L0 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))"
  defines "L1 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))"
  defines "L2 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))"
  defines "L3 ≡
      (∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
    + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      L0 =
        c00*y0' + c10*y1' + c20*y2' + c30*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))
    ∧ L1 =
        c01*y0' + c11*y1' + c21*y2' + c31*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))
    ∧ L2 =
        c02*y0' + c12*y1' + c22*y2' + c32*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))
    ∧ L3 =
        c03*y0' + c13*y1' + c23*y2' + c33*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
proof -
  obtain c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33
    where coeffs:
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0' + c10*y1' + c20*y2' + c30*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0' + c11*y1' + c21*y2' + c31*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0' + c12*y1' + c22*y2' + c32*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0' + c13*y1' + c23*y2' + c33*y3' +
        (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_last_four_Li_linear_combinations[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  show ?thesis
  proof (intro exI conjI)
    show "L0 =
        c00*y0' + c10*y1' + c20*y2' + c30*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 4)) * x $$ (h, 0))"
      unfolding L0_def
      using coeffs(1)
      by simp

    show "L1 =
        c01*y0' + c11*y1' + c21*y2' + c31*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 3)) * x $$ (h, 0))"
      unfolding L1_def
      using coeffs(2)
      by simp

    show "L2 =
        c02*y0' + c12*y1' + c22*y2' + c32*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 2)) * x $$ (h, 0))"
      unfolding L2_def
      using coeffs(3)
      by simp

    show "L3 =
        c03*y0' + c13*y1' + c23*y2' + c33*y3'
        + (∑h = 4..<m. rat_of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
        + (∑h = m..<𝗏. rat_of_int (N $$ (h, m - 1)) * x $$ (h, 0))"
      unfolding L3_def
      using coeffs(4)
      by simp
  qed
qed

lemma brc_L0_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c00 c10 c20 c30.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
proof -
  have i3_in: "(3::nat) ∈ {0..<4}" by simp

  obtain c00 c10 c20 c30 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
      c00*y0 + c10*y1 + c20*y2 + c30*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i3_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 3 - 1 = m - 4"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L1_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c01 c11 c21 c31.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
proof -
  have i2_in: "(2::nat) ∈ {0..<4}" by simp

  obtain c01 c11 c21 c31 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
      c01*y0 + c11*y1 + c21*y2 + c31*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i2_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 2 - 1 = m - 3"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L2_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃c02 c12 c22 c32.
    (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
proof -
  have i1_in: "(1::nat) ∈ {0..<4}" by simp

  obtain c02 c12 c22 c32 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i1_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 1 - 1 = m - 2"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L3_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
shows
  "∃c03 c13 c23 c33.
    (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have i0_in: "(0::nat) ∈ {0..<4}" by simp

  obtain c03 c13 c23 c33 where coeff:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
  proof -
    obtain e0 e1 e2 e3 where e:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0)) =
       e0*y0 + e1*y1 + e2*y2 + e3*y3 +
       (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 0 - 1)) * x $$ (m - h - 1, 0))"
      using linear_comb_of_y_part_2[
        OF four_sq m_v m_gt3 i0_in
           x0_def x1_def x2_def x3_def
           x0_eq x1_eq x2_eq x3_eq]
      by blast

    have simp_col: "m - 0 - 1 = m - 1"
      using m_gt3 by simp

    show ?thesis
      using e simp_col that by simp
  qed

  show ?thesis
    using coeff by blast
qed

lemma brc_L0123_from_last_four:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  obtain c00 c10 c20 c30 where L0:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
      c00*y0 + c10*y1 + c20*y2 + c30*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
    using brc_L0_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c01 c11 c21 c31 where L1:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
      c01*y0 + c11*y1 + c21*y2 + c31*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
    using brc_L1_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c02 c12 c22 c32 where L2:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
      c02*y0 + c12*y1 + c22*y2 + c32*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
    using brc_L2_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  obtain c03 c13 c23 c33 where L3:
    "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
      c03*y0 + c13*y1 + c23*y2 + c33*y3 +
      (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L3_from_last_four[
      OF four_sq m_v m_gt3 x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  show ?thesis
    using L0 L1 L2 L3 by blast
qed

lemma brc_last_four_square_if_choices:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 =
        (if e00 = 1 then
          - (e10*y1 + e20*y2 + e30*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
         else
          (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))
      ∧ y1 =
        (if e11 = 1 then
          - (e01*y0 + e21*y2 + e31*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
         else
          (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))
      ∧ y2 =
        (if e22 = 1 then
          - (e02*y0 + e12*y1 + e32*y3 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
         else
          (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))
      ∧ y3 =
        (if e33 = 1 then
          - (e03*y0 + e13*y1 + e23*y2 +
             (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
             (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
         else
          (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
      (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  obtain e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
    where Ls:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L0123_from_last_four[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  have ch_all:
    "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))
    ∧ y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))
    ∧ y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))
    ∧ y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
    using choices[OF Ls] .

  have ch0: "y0 =
      (if e00 = 1 then
        - (e10*y1 + e20*y2 + e30*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
       else
        (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"
    using ch_all by blast

  have ch1: "y1 =
      (if e11 = 1 then
        - (e01*y0 + e21*y2 + e31*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
       else
        (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"
    using ch_all by blast

  have ch2: "y2 =
      (if e22 = 1 then
        - (e02*y0 + e12*y1 + e32*y3 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
       else
        (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"
    using ch_all by blast

  have ch3: "y3 =
      (if e33 = 1 then
        - (e03*y0 + e13*y1 + e23*y2 +
           (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
       else
        (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"
    using ch_all by blast

  show ?thesis
    using induction_step_0123_explicit[
      OF Ls(1) Ls(2) Ls(3) Ls(4) ch0 ch1 ch2 ch3]
    .
qed

definition brc_choice0 where
  "brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m =
    (if e00 = 1 then
      - (e10*y1 + e20*y2 + e30*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / 2
     else
      (e10*y1 + e20*y2 + e30*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00))"

definition brc_choice1 where
  "brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m =
    (if e11 = 1 then
      - (e01*y0 + e21*y2 + e31*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / 2
     else
      (e01*y0 + e21*y2 + e31*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11))"

definition brc_choice2 where
  "brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m =
    (if e22 = 1 then
      - (e02*y0 + e12*y1 + e32*y3 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / 2
     else
      (e02*y0 + e12*y1 + e32*y3 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22))"

definition brc_choice3 where
  "brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m =
    (if e33 = 1 then
      - (e03*y0 + e13*y1 + e23*y2 +
         (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
         (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / 2
     else
      (e03*y0 + e13*y1 + e23*y2 +
       (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33))"

lemma induction_step_0123_choices:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  assumes ch0: "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes ch1: "y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes ch2: "y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes ch3: "y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0123_explicit[
    OF L0 L1 L2 L3]
  using ch0 ch1 ch2 ch3
  unfolding brc_choice0_def brc_choice1_def brc_choice2_def brc_choice3_def
  by blast

lemma brc_last_four_square_if_choices_short:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
    ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
    ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
    ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  obtain e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33
    where Ls:
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))"
      "(∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_L0123_from_last_four[
      OF four_sq m_v m_gt3
         x0_def x1_def x2_def x3_def
         x0_eq x1_eq x2_eq x3_eq]
    by blast

  have ch_all:
    "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
   ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
   ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
   ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
    using choices[OF Ls] .

  show ?thesis
    using induction_step_0123_choices[
      OF Ls(1) Ls(2) Ls(3) Ls(4)]
    using ch_all
    by blast
qed

lemma brc_choice0_exists:
  fixes e00 e10 e20 e30 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y0. y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  by blast

lemma brc_choice1_exists:
  fixes e01 e11 e21 e31 y0 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y1. y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  by blast

lemma brc_choice2_exists:
  fixes e02 e12 e22 e32 y0 y1 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y2. y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  by blast

lemma brc_choice3_exists:
  fixes e03 e13 e23 e33 y0 y1 y2 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  shows "∃y3. y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  by blast

lemma brc_choice0_square:
  fixes e00 e10 e20 e30 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y0 ≡ brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
  using induction_step_0_explicit[OF L0]
  unfolding y0_def brc_choice0_def
  by simp

lemma brc_choice1_square:
  fixes e01 e11 e21 e31 y0 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y1 ≡ brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  shows
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
  using induction_step_1_explicit[OF L1]
  unfolding y1_def brc_choice1_def
  by simp

lemma brc_choice2_square:
  fixes e02 e12 e22 e32 y0 y1 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y2 ≡ brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  shows
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
  using induction_step_2_explicit[OF L2]
  unfolding y2_def brc_choice2_def
  by simp

lemma brc_choice3_square:
  fixes e03 e13 e23 e33 y0 y1 y2 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y3 ≡ brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_3_explicit[OF L3]
  unfolding y3_def brc_choice3_def
  by simp

lemma brc_choice0123_square:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes y0_def: "y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m"
  assumes y1_def: "y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m"
  assumes y2_def: "y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m"
  assumes y3_def: "y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1 + e20*y2 + e30*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2 + e31*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using induction_step_0123_choices[
    OF L0 L1 L2 L3 y0_def y1_def y2_def y3_def]
  . 

lemma brc_last_four_square_from_choices:
  fixes a b c d m :: nat
  fixes x :: "rat mat"
  fixes y0 y1 y2 y3 :: rat
  fixes x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "𝗏 ≥ m"
  assumes m_gt3: "m > 3"
  assumes x0_def: "x0 = x $$ (m - 4, 0)"
  assumes x1_def: "x1 = x $$ (m - 3, 0)"
  assumes x2_def: "x2 = x $$ (m - 2, 0)"
  assumes x3_def: "x3 = x $$ (m - 1, 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes choices:
    "⋀e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33.
      ⟦
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        e00*y0 + e10*y1 + e20*y2 + e30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        e01*y0 + e11*y1 + e21*y2 + e31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        e02*y0 + e12*y1 + e22*y2 + e32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0));
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        e03*y0 + e13*y1 + e23*y2 + e33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))
      ⟧ ⟹
      y0 = brc_choice0 e00 e10 e20 e30 y1 y2 y3 x m
    ∧ y1 = brc_choice1 e01 e11 e21 e31 y0 y2 y3 x m
    ∧ y2 = brc_choice2 e02 e12 e22 e32 y0 y1 y3 x m
    ∧ y3 = brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
  using brc_last_four_square_if_choices_short[
    OF four_sq m_v m_gt3
       x0_def x1_def x2_def x3_def
       x0_eq x1_eq x2_eq x3_eq choices]
  .

lemma brc_sequential_elimination_step:
  fixes e00 e10 e20 e30 e01 e11 e21 e31 e02 e12 e22 e32 e03 e13 e23 e33 :: rat
  fixes y1a y2a y3a :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  defines "y0 ≡ brc_choice0 e00 e10 e20 e30 y1a y2a y3a x m"
  defines "y1 ≡ brc_choice1 e01 e11 e21 e31 y0 y2a y3a x m"
  defines "y2 ≡ brc_choice2 e02 e12 e22 e32 y0 y1 y3a x m"
  defines "y3 ≡ brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m"
  assumes L0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*y0 + e10*y1a + e20*y2a + e30*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
  assumes L1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*y1 + e21*y2a + e31*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  assumes L2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1 + e22*y2 + e32*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
  assumes L3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  shows
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2
    ∧ y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2
    ∧ y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2
    ∧ y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have L0': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
      e00*(brc_choice0 e00 e10 e20 e30 y1a y2a y3a x m)
      + e10*y1a + e20*y2a + e30*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using L0 unfolding y0_def by simp

  have S0:
    "y0^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0)))^2"
    using brc_choice0_square[OF L0']
    unfolding y0_def by simp

  have L1': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) =
      e01*y0 + e11*(brc_choice1 e01 e11 e21 e31 y0 y2a y3a x m)
      + e21*y2a + e31*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using L1 unfolding y1_def by simp

  have S1:
    "y1^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0)))^2"
    using brc_choice1_square[OF L1']
    unfolding y1_def by simp

  have L2': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) =
      e02*y0 + e12*y1
      + e22*(brc_choice2 e02 e12 e22 e32 y0 y1 y3a x m)
      + e32*y3a +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
    using L2 unfolding y2_def by simp

  have S2:
    "y2^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0)))^2"
    using brc_choice2_square[OF L2']
    unfolding y2_def by simp

  have L3': "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) =
      e03*y0 + e13*y1 + e23*y2
      + e33*(brc_choice3 e03 e13 e23 e33 y0 y1 y2 x m) +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using L3 unfolding y3_def by simp

  have S3:
    "y3^2 =
      ((∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
       (∑h∈{m..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0)))^2"
    using brc_choice3_square[OF L3']
    unfolding y3_def by simp

  show ?thesis
    using S0 S1 S2 S3 by blast
qed

lemma y_inv_norm_brc:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  shows
    "let xs = y_inv_of ((a,b,c,d),(y0,y1,y2,y3)) in
      of_nat (𝗄 - Λ) *
        (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
      =
      y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have nz: "a^2 + b^2 + c^2 + d^2 ≠ 0"
    using four_sq blocksize_gt_index by simp

  have yback:
    "y_of ((a,b,c,d), ?xs) = (y0,y1,y2,y3)"
    using y_inverses_part_2[OF nz, of y0 y1 y2 y3]
    by simp

  have norm:
    "let y = y_of ((a,b,c,d), ?xs) in
      one_of y ^ 2 + two_of y ^ 2 + three_of y ^ 2 + four_of y ^ 2
      =
      of_nat (𝗄 - Λ) *
        (one_of ?xs^2 + two_of ?xs^2 + three_of ?xs^2 + four_of ?xs^2)"
    using y_of_norm_brc[OF four_sq,
      of "one_of ?xs" "two_of ?xs" "three_of ?xs" "four_of ?xs"]
    by (simp add: Let_def)

  show ?thesis
    using norm yback
    by (simp add: Let_def)
qed

lemma y_norm_replace_brc:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have norm:
    "of_nat (𝗄 - Λ) *
      (one_of ?xs^2 + two_of ?xs^2 + three_of ?xs^2 + four_of ?xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_inv_norm_brc[OF four_sq, of y0 y1 y2 y3]
    by (simp add: Let_def)

  show ?thesis
    using norm x0_eq x1_eq x2_eq x3_eq
    by simp
qed

lemma brc_four_var_identity_y:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  defines "xs ≡ y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have base:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of xs
           else if i = m - 3 then two_of xs
           else if i = m - 2 then three_of xs
           else if i = m - 1 then four_of xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of xs + two_of xs + three_of xs + four_of xs)^2
    + of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)"
    using brc_v_1_mod_4_identity[
      OF four_sq m_props,
      of "one_of xs" "two_of xs" "three_of xs" "four_of xs"]
    by simp

  have norm:
    "of_int (int (𝗄 - Λ)) *
      (one_of xs^2 + two_of xs^2 + three_of xs^2 + four_of xs^2)
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    unfolding xs_def
    using y_inv_norm_brc[OF four_sq, of y0 y1 y2 y3]
    by (simp add: Let_def)

  show ?thesis
    using base norm by simp
qed

lemma brc_four_var_identity_y_named:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?xs = "y_inv_of ((a,b,c,d),(y0,y1,y2,y3))"

  have main:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) *
      (mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then one_of ?xs
           else if i = m - 3 then two_of ?xs
           else if i = m - 2 then three_of ?xs
           else if i = m - 1 then four_of ?xs
           else 0)
        else 0)) $$ (h,0))^2)
    =
    of_int (int Λ) *
      (one_of ?xs + two_of ?xs + three_of ?xs + four_of ?xs)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
    using brc_four_var_identity_y[OF four_sq m_props, of y0 y1 y2 y3]
    by simp

  have xs0: "one_of ?xs = x0"
    using x0_eq by simp
  have xs1: "two_of ?xs = x1"
    using x1_eq by simp
  have xs2: "three_of ?xs = x2"
    using x2_eq by simp
  have xs3: "four_of ?xs = x3"
    using x3_eq by simp

  have sum_eq:
    "one_of ?xs + two_of ?xs + three_of ?xs + four_of ?xs
     = x0 + x1 + x2 + x3"
    using x0_eq x1_eq x2_eq x3_eq
    by simp

  have inner_eq:
    "⋀h. (if h = m - 4 then one_of ?xs
          else if h = m - 3 then two_of ?xs
          else if h = m - 2 then three_of ?xs
          else if h = m - 1 then four_of ?xs
          else 0)
       =
         (if h = m - 4 then x0
          else if h = m - 3 then x1
          else if h = m - 2 then x2
          else if h = m - 1 then x3
          else 0)"
    using xs0 xs1 xs2 xs3
    by auto

  show ?thesis
    using main inner_eq sum_eq
    by simp
qed

lemma brc_four_var_identity_for_sparse_x:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
  unfolding x_def
  using brc_four_var_identity_y_named[
    OF four_sq m_props x0_eq x1_eq x2_eq x3_eq]
  by simp

lemma sparse_x_last_four_entries:
  fixes x :: "rat mat"
  fixes x0 x1 x2 x3 :: rat
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  shows
    "x $$ (m - 4,0) = x0"
    "x $$ (m - 3,0) = x1"
    "x $$ (m - 2,0) = x2"
    "x $$ (m - 1,0) = x3"
proof -
  have m4: "4 ≤ m"
    using m_props by simp

  show "x $$ (m - 4,0) = x0"
    unfolding x_def using m_props m4 by simp

  show "x $$ (m - 3,0) = x1"
    unfolding x_def using m_props m4 by auto

  show "x $$ (m - 2,0) = x2"
    unfolding x_def using m_props m4 by auto

  show "x $$ (m - 1,0) = x3"
    unfolding x_def using m_props m4 by auto
qed

lemma brc_sparse_x_L0123:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
proof -
  have entries:
    "x $$ (m - 4,0) = x0"
    "x $$ (m - 3,0) = x1"
    "x $$ (m - 2,0) = x2"
    "x $$ (m - 1,0) = x3"
    using sparse_x_last_four_entries[OF m_props x_def] .

  have entries_rev:
    "x0 = x $$ (m - 4,0)"
    "x1 = x $$ (m - 3,0)"
    "x2 = x $$ (m - 2,0)"
    "x3 = x $$ (m - 1,0)"
    using entries by simp_all

  show ?thesis
    using brc_L0123_from_last_four[
      OF four_sq m_props(2) m_props(1)
         entries_rev(1) entries_rev(2) entries_rev(3) entries_rev(4)
         x0_eq x1_eq x2_eq x3_eq]
    .
qed

lemma brc_sparse_x_identity_and_coeffs:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 x0 x1 x2 x3 :: rat
  fixes x :: "rat mat"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  assumes x_def:
    "x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2
    ∧
    (∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)))"
proof -
  have id:
   "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_int (int Λ) * (x0 + x1 + x2 + x3)^2
    + y0^2 + y1^2 + y2^2 + y3^2"
    using brc_four_var_identity_for_sparse_x[
      OF four_sq m_props x_def x0_eq x1_eq x2_eq x3_eq] .

  have coeffs:
    "∃c00 c10 c20 c30 c01 c11 c21 c31 c02 c12 c22 c32 c03 c13 c23 c33.
      (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0)) =
        c00*y0 + c10*y1 + c20*y2 + c30*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 4)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0)) =
        c01*y0 + c11*y1 + c21*y2 + c31*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 3)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0)) =
        c02*y0 + c12*y1 + c22*y2 + c32*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 2)) * x $$ (m - h - 1, 0))
    ∧ (∑h = 0..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0)) =
        c03*y0 + c13*y1 + c23*y2 + c33*y3 +
        (∑h = 4..<m. of_int (N $$ (m - h - 1, m - 1)) * x $$ (m - h - 1, 0))"
    using brc_sparse_x_L0123[
      OF four_sq m_props x_def x0_eq x1_eq x2_eq x3_eq] .

  show ?thesis
    using id coeffs by blast
qed

lemma brc_sparse_x_identity_exists:
  fixes a b c d m :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_props: "m > 3" "𝗏 ≥ m"
  shows
   "∃(x :: rat mat) (x0 :: rat) (x1 :: rat) (x2 :: rat) (x3 :: rat).
      x = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then x0
           else if i = m - 3 then x1
           else if i = m - 2 then x2
           else if i = m - 1 then x3
           else 0)
        else 0)
    ∧ x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧ x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))
    ∧
      (∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
      =
      of_int (int Λ) * (x0 + x1 + x2 + x3)^2
      + y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?x0 = "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x1 = "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x2 = "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x3 = "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?X = "mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then ?x0
           else if i = m - 3 then ?x1
           else if i = m - 2 then ?x2
           else if i = m - 1 then ?x3
           else 0)
        else 0)"

  have Xdef:
    "?X = mat 𝗏 1 (λ(i,j).
        if j = 0 then
          (if i = m - 4 then ?x0
           else if i = m - 3 then ?x1
           else if i = m - 2 then ?x2
           else if i = m - 1 then ?x3
           else 0)
        else 0)"
    by simp

  have x0eq: "?x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x1eq: "?x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x2eq: "?x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp
  have x3eq: "?x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))" by simp

  have id:
    "(∑i∈{0..<𝗏}. (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * ?X $$ (h,0))^2)
      =
      of_int (int Λ) * (?x0 + ?x1 + ?x2 + ?x3)^2
      + y0^2 + y1^2 + y2^2 + y3^2"
    by (rule brc_four_var_identity_for_sparse_x[
        OF four_sq m_props Xdef x0eq x1eq x2eq x3eq])

  show ?thesis
    using id by blast
qed

lemma brc_simplified_to_y:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 y0 y1 y2 y3 :: rat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes brc_simplified:
    "B =
       of_int (int Λ) * (x0 + x1 + x2 + x3)^2 +
       of_int (int (𝗄 - Λ)) * (x0^2 + x1^2 + x2^2 + x3^2)"
  assumes x0_eq: "x0 = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_eq: "x1 = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_eq: "x2 = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_eq: "x3 = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "B =
       of_int (int Λ) * (x0 + x1 + x2 + x3)^2 +
       y0^2 + y1^2 + y2^2 + y3^2"
  using brc_simplified
        y_norm_replace_brc[OF four_sq x0_eq x1_eq x2_eq x3_eq]
  by simp

lemma sum_last_four:
  fixes f :: "nat ⇒ rat"
  assumes m4: "4 ≤ m"
  shows "(∑j = m - 4..<m. f j) =
    f (m - 4) + f (m - 3) + f (m - 2) + f (m - 1)"
proof -
  have a1: "Suc (m - 4) = m - 3"
    using m4 by simp
  have a2: "Suc (Suc (m - 4)) = m - 2"
    using m4 by simp
  have a3: "Suc (Suc (Suc (m - 4))) = m - 1"
    using m4 by simp

  have "(∑j = m - 4..<m. f j)
      = f (m - 4) + f (Suc (m - 4)) + f (Suc (Suc (m - 4))) +
        f (Suc (Suc (Suc (m - 4))))"
    using m4
    by (subst sum.atLeast_Suc_lessThan, simp_all)+

  then show ?thesis
    using a1 a2 a3
    by simp
qed

lemma sumsq_split_last_four:
  fixes f :: "nat ⇒ rat"
  assumes m4: "4 ≤ m"
  shows
   "(∑j = 0..<m. (f j)^2)
    =
    (∑j = 0..<m-4. (f j)^2)
    + (f (m - 4))^2
    + (f (m - 3))^2
    + (f (m - 2))^2
    + (f (m - 1))^2"
proof -
  have
   "(∑j = 0..<m. (f j)^2)
    =
    (∑j = 0..<m-4. (f j)^2)
    +
    (∑j = m-4..<m. (f j)^2)"
    using m4
    by (simp add: sum.atLeastLessThan_concat)

  also have
   "... =
    (∑j = 0..<m-4. (f j)^2)
    +
    ((f (m - 4))^2
     + (f (m - 3))^2
     + (f (m - 2))^2
     + (f (m - 1))^2)"
    using sum_last_four[OF m4, of "λj. (f j)^2"]
    by simp

  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma brc_linear_sum_split_last_four:
  fixes x :: "rat mat"
  assumes m4: "4 ≤ m"
  defines "L ≡ λj. ∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0)"
  shows
   "(∑j = 0..<m. (L j)^2)
    =
    (∑j = 0..<m-4. (L j)^2)
    + (L (m - 4))^2
    + (L (m - 3))^2
    + (L (m - 2))^2
    + (L (m - 1))^2"
  using sumsq_split_last_four[OF m4, of L]
  by simp

lemma brc_linear_sum_split_last_four_expanded:
  fixes x :: "rat mat"
  assumes m4: "4 ≤ m"
  shows
   "(∑j = 0..<m.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0))^2)
    =
    (∑j = 0..<m-4.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,j)) * x $$ (h,0))^2)
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-4)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-3)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-2)) * x $$ (h,0))^2
    + (∑h∈{0..<𝗏}. of_int (N $$ (h,m-1)) * x $$ (h,0))^2"
  using brc_linear_sum_split_last_four[OF m4, of x]
  by simp

definition brc_descent_invariant :: "nat ⇒ bool" where
  "brc_descent_invariant m ⟷
    (∃q0 q1 q2 :: rat.
      (q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) ∧
      q0^2 =
        of_nat (𝗄 - Λ) * q1^2 +
        of_nat Λ * q2^2)"

definition brc_descent_form :: "nat ⇒ rat mat ⇒ rat ⇒ bool" where
  "brc_descent_form m x C ⟷
    C =
      (∑i∈{0..<m}.
        (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"

definition brc_linear_form :: "rat mat ⇒ nat ⇒ rat" where
  "brc_linear_form x i =
    (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"

definition brc_square_sum_upto :: "nat ⇒ rat mat ⇒ rat" where
  "brc_square_sum_upto m x =
    (∑i∈{0..<m}. (brc_linear_form x i)^2)"

definition brc_tail_equation :: "nat ⇒ rat mat ⇒ rat ⇒ rat ⇒ bool" where
  "brc_tail_equation m x Y Z ⟷
    brc_square_sum_upto m x =
      of_nat Λ * Z^2 + Y"

lemma brc_tail_equationI:
  assumes
    "brc_square_sum_upto m x = of_nat Λ * Z^2 + Y"
  shows "brc_tail_equation m x Y Z"
  using assms
  unfolding brc_tail_equation_def
  by simp

lemma brc_tail_equationD:
  assumes "brc_tail_equation m x Y Z"
  shows "brc_square_sum_upto m x = of_nat Λ * Z^2 + Y"
  using assms
  unfolding brc_tail_equation_def
  by simp

lemma brc_tail_equation_full:
  fixes x :: "rat mat"
  shows
    "brc_tail_equation 𝗏 x
      (of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2))
      (∑j∈{0..<𝗏}. x $$ (j,0))"
proof -
  have
    "brc_square_sum_upto 𝗏 x =
      of_nat Λ * (∑j∈{0..<𝗏}. x $$ (j,0))^2 +
      of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
    unfolding brc_square_sum_upto_def brc_linear_form_def
    using brc_x_equation[of x]
    by simp
  then show ?thesis
    unfolding brc_tail_equation_def
    by (simp add: algebra_simps)
qed

lemma brc_v_eq_4w_plus_1:
  assumes "𝗏 mod 4 = 1"
  shows "∃w. 𝗏 = 4 * w + 1"
proof
  show "𝗏 = 4 * (𝗏 div 4) + 1"
    using assms
    by (metis div_mult_mod_eq mult.commute)
qed


lemma y_norm_identity:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes n_def: "n = a^2 + b^2 + c^2 + d^2"
  shows
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat n * (x0^2 + x1^2 + x2^2 + x3^2)"
  unfolding n_def
  by (simp add: algebra_simps power2_eq_square)

lemma y_norm_identity_k_lambda:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)"
  using y_norm_identity[of "𝗄 - Λ" a b c d x0 x1 x2 x3] abcd
  by simp

lemma y_block_sum_identity:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (x0^2 + x1^2 + x2^2 + x3^2)
     =
     (one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2"
  using y_norm_identity_k_lambda[OF abcd, of x0 x1 x2 x3]
  by simp

lemma y_first_block_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
      ((x $$ (0,0))^2 + (x $$ (1,0))^2 + (x $$ (2,0))^2 + (x $$ (3,0))^2)
     =
     (one_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (0,0), x $$ (1,0), x $$ (2,0), x $$ (3,0)))))^2"
  using y_block_sum_identity[OF abcd,
      of "x $$ (0,0)" "x $$ (1,0)" "x $$ (2,0)" "x $$ (3,0)"]
  by simp

lemma y_block_h_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
      ((x $$ (4*h,0))^2 +
       (x $$ (4*h + 1,0))^2 +
       (x $$ (4*h + 2,0))^2 +
       (x $$ (4*h + 3,0))^2)
     =
     (one_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0), x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2"
  using y_block_sum_identity[OF abcd,
      of "x $$ (4*h,0)"
         "x $$ (4*h + 1,0)"
         "x $$ (4*h + 2,0)"
         "x $$ (4*h + 3,0)"]
  by simp

definition y_block :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_block a b c d x i =
    (let h = i div 4;
         r = i mod 4;
         y = y_of ((a,b,c,d),
              (x $$ (4*h,0),
               x $$ (4*h + 1,0),
               x $$ (4*h + 2,0),
               x $$ (4*h + 3,0)))
     in if r = 0 then one_of y
        else if r = 1 then two_of y
        else if r = 2 then three_of y
        else four_of y)"

lemma y_block_4h_1:
  "y_block a b c d x (4*h + 1) =
   two_of (y_of ((a,b,c,d),
     (x $$ (4*h,0), x $$ (4*h + 1,0),
      x $$ (4*h + 2,0), x $$ (4*h + 3,0))))"
proof -
  have div_eq: "Suc (4*h) div 4 = h"
    by simp
  have mod_eq: "Suc (4*h) mod 4 = 1"
    by simp
  show ?thesis
    unfolding y_block_def Let_def
    using div_eq mod_eq
    by simp
qed

lemma y_block_4h_3:
  "y_block a b c d x (4*h + 3) =
   four_of (y_of ((a,b,c,d),
     (x $$ (4*h,0), x $$ (4*h + 1,0),
      x $$ (4*h + 2,0), x $$ (4*h + 3,0))))"
  unfolding y_block_def
  by simp

definition x_block_sqsum :: "rat mat ⇒ nat ⇒ rat" where
  "x_block_sqsum x h =
     (x $$ (4*h,0))^2 +
     (x $$ (4*h + 1,0))^2 +
     (x $$ (4*h + 2,0))^2 +
     (x $$ (4*h + 3,0))^2"

definition y_block_sqsum :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_block_sqsum a b c d x h =
     (one_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (two_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (three_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2 +
     (four_of (y_of ((a,b,c,d),
        (x $$ (4*h,0), x $$ (4*h + 1,0),
         x $$ (4*h + 2,0), x $$ (4*h + 3,0)))))^2"

lemma y_block_sqsum_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows "of_nat (𝗄 - Λ) * x_block_sqsum x h =
         y_block_sqsum a b c d x h"
  unfolding x_block_sqsum_def y_block_sqsum_def
  using y_block_h_identity[OF abcd, of x h]
  by simp

lemma y_blocks_sqsum_identity:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)
     =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"
proof -
  have "⋀h. h ∈ {0..<w} ⟹
    of_nat (𝗄 - Λ) * x_block_sqsum x h =
    y_block_sqsum a b c d x h"
    using y_block_sqsum_identity[OF abcd] by simp
  then have
    "(∑h∈{0..<w}. of_nat (𝗄 - Λ) * x_block_sqsum x h)
     =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"
    by simp
  then show ?thesis
    by (simp add: sum_distrib_left)
qed

lemma brc_x_sum_split_4w_last:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)
     =
     (∑j∈{0..<4*w}. (x $$ (j,0))^2) + (x $$ (4*w,0))^2"
proof -
  have "𝗏 = Suc (4*w)"
    using v_form by simp
  then show ?thesis
    by (simp add: sum.atLeast0_lessThan_Suc)
qed

lemma brc_x_sum_split_4w_last_plain:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
    "(∑j∈{0..<𝗏}. x $$ (j,0))
     =
     (∑j∈{0..<4*w}. x $$ (j,0)) + x $$ (4*w,0)"
proof -
  have "𝗏 = Suc (4*w)"
    using v_form by simp
  then show ?thesis
    by (simp add: sum.atLeast0_lessThan_Suc)
qed

lemma brc_x_equation_split:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ *
      ((∑j∈{0..<4*w}. x $$ (j,0))
        + x $$ (4*w,0))^2
    +
    of_nat (𝗄 - Λ) *
      ((∑j∈{0..<4*w}. (x $$ (j,0))^2)
        + (x $$ (4*w,0))^2)"
proof -
  have eq:
    "(∑i∈{0..<𝗏}.
    (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (∑j∈{0..<𝗏}. x $$ (j,0))^2
    +
    of_nat (𝗄 - Λ) * (∑j∈{0..<𝗏}. (x $$ (j,0))^2)"
    using brc_x_equation[of x]
    by simp

  have sq:
    "(∑j∈{0..<𝗏}. (x $$ (j,0))^2)
     =
     (∑j∈{0..<4*w}. (x $$ (j,0))^2)
      + (x $$ (4*w,0))^2"
    using brc_x_sum_split_4w_last[OF v_form] .

  have lin:
    "(∑j∈{0..<𝗏}. x $$ (j,0))
     =
     (∑j∈{0..<4*w}. x $$ (j,0))
      + x $$ (4*w,0)"
    using brc_x_sum_split_4w_last_plain[OF v_form] .

  show ?thesis
    using eq sq lin
    by simp
qed

definition x_head_sum :: "rat mat ⇒ nat ⇒ rat" where
  "x_head_sum x w = (∑j∈{0..<4*w}. x $$ (j,0))"

definition x_head_sqsum :: "rat mat ⇒ nat ⇒ rat" where
  "x_head_sqsum x w = (∑j∈{0..<4*w}. (x $$ (j,0))^2)"

definition x_last :: "rat mat ⇒ nat ⇒ rat" where
  "x_last x w = x $$ (4*w,0)"

lemma brc_x_equation_split_named:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    of_nat (𝗄 - Λ) *
      (x_head_sqsum x w + (x_last x w)^2)"
  using brc_x_equation_split[OF v_form, of x]
  unfolding x_head_sum_def x_head_sqsum_def x_last_def
  by simp

definition y_blocks_sqsum :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ rat" where
  "y_blocks_sqsum a b c d x w =
     (∑h∈{0..<w}. y_block_sqsum a b c d x h)"

lemma y_blocks_sqsum_identity_named:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)
     =
     y_blocks_sqsum a b c d x w"
  using y_blocks_sqsum_identity[OF abcd, of x w]
  unfolding y_blocks_sqsum_def
  by simp

lemma brc_x_equation_transformed_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes head_blocks:
    "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"
proof -
  have split_eq:
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    of_nat (𝗄 - Λ) *
      (x_head_sqsum x w + (x_last x w)^2)"
    using brc_x_equation_split_named[OF v_form, of x] .

  have block_eq:
    "of_nat (𝗄 - Λ) * x_head_sqsum x w =
     y_blocks_sqsum a b c d x w"
  proof -
    have "of_nat (𝗄 - Λ) * x_head_sqsum x w =
          of_nat (𝗄 - Λ) * (∑h∈{0..<w}. x_block_sqsum x h)"
      using head_blocks by simp
    also have "... = y_blocks_sqsum a b c d x w"
      using y_blocks_sqsum_identity_named[OF abcd, of x w] .
    finally show ?thesis .
  qed

  show ?thesis
    using split_eq block_eq
    by (simp add: algebra_simps)
qed

definition transformed_identity where
  "transformed_identity a b c d x w ≡
   (∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"

lemma transformed_identity_exists:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes head_blocks:
    "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
  shows "transformed_identity a b c d x w"
  using brc_x_equation_transformed_conditional[
      OF v_form abcd head_blocks]
  unfolding transformed_identity_def
  by simp

lemma sum_first_4_Suc_split:
  fixes f :: "nat ⇒ rat"
  shows "(∑j = 0..<4 + n * 4. f j)
       =
       f (n * 4) + f (Suc (n * 4)) +
       f (Suc (Suc (n * 4))) + f (3 + n * 4) +
       (∑j = 0..<n * 4. f j)"
proof -
  have "(∑j = 0..<4 + n * 4. f j)
      = (∑j = 0..<n * 4. f j) + (∑j = n * 4..<4 + n * 4. f j)"
    by (simp add: sum.atLeastLessThan_concat)
  also have "(∑j = n * 4..<4 + n * 4. f j)
      = f (n * 4) + f (Suc (n * 4)) + f (Suc (Suc (n * 4))) + f (3 + n * 4)"
    by (simp add: numeral_eq_Suc)
  finally show ?thesis
    by (simp add: algebra_simps)
qed

lemma sum_x_first_4w_as_blocks:
  fixes x :: "rat mat"
  shows "x_head_sqsum x w = (∑h∈{0..<w}. x_block_sqsum x h)"
proof (induct w)
  case 0
  show ?case
    unfolding x_head_sqsum_def x_block_sqsum_def
    by simp
next
  case (Suc n)
  have IH:
    "x_head_sqsum x n = (∑h∈{0..<n}. x_block_sqsum x h)"
    using Suc.hyps by simp

  have split:
    "x_head_sqsum x (Suc n)
     =
     x_head_sqsum x n + x_block_sqsum x n"
    unfolding x_head_sqsum_def x_block_sqsum_def
    using sum_first_4_Suc_split[of "λj. (x $$ (j,0))^2" n]
    by (simp add: algebra_simps)

  show ?case
    using IH split
    by simp
qed

lemma brc_x_equation_transformed:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
   "(∑i∈{0..<𝗏}.
      (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))^2)
    =
    of_nat Λ * (x_head_sum x w + x_last x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (x_last x w)^2"
  using brc_x_equation_transformed_conditional[
    OF v_form abcd sum_x_first_4w_as_blocks]
  by simp

lemma choose_y_square_cancel:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
proof (cases "e = 1")
  case True
  have "(e * (-rest/2) + rest)^2 = (-rest/2)^2"
    using True
    by (simp add: power2_eq_square algebra_simps)
  thus ?thesis
    by blast
next
  case False
  let ?y = "rest / (1 - e)"

  have nz: "1 - e ≠ 0"
    using False by simp

  have lhs:
    "e * ?y + rest = ?y"
  proof -
    have "e * (rest/(1-e)) + rest
        = (e*rest + rest*(1-e)) / (1-e)"
      using nz
      by (simp add: divide_simps)
    also have "... = rest/(1-e)"
      by (simp add: algebra_simps)
    finally show ?thesis
      by simp
  qed

  have "(e * ?y + rest)^2 = ?y^2"
    using lhs by simp
  thus ?thesis
    by blast
qed

lemma eliminate_one_square_from_equation:
  fixes e rest RHS :: rat
  assumes eq: "(e * y + rest)^2 + T = y^2 + RHS"
  assumes cancel: "(e * y + rest)^2 = y^2"
  shows "T = RHS"
  using eq cancel
  by simp

lemma eliminate_square_from_sum:
  fixes f :: "nat ⇒ rat"
  assumes i_mem: "i ∈ A"
  assumes cancel: "L^2 = f i^2"
  assumes eq:
    "L^2 + (∑j∈A - {i}. f j^2) = f i^2 + RHS"
  shows "(∑j∈A - {i}. f j^2) = RHS"
  using eq cancel
  by simp

lemma eliminate_last_square_from_interval:
  fixes f :: "nat ⇒ rat"
  assumes cancel: "L^2 = f n^2"
  assumes eq:
    "L^2 + (∑j∈{0..<n}. f j^2) = f n^2 + RHS"
  shows "(∑j∈{0..<n}. f j^2) = RHS"
  using eq cancel
  by simp

lemma brc_final_rat_from_reduced_identity:
  fixes Lv y0 yv :: rat
  assumes red:
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
  assumes nz:
    "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows
    "∃q0 q1 q2 :: rat.
       (q0 ≠ 0 ∨ q1 ≠ 0 ∨ q2 ≠ 0) ∧
       q0^2 = of_nat (𝗄 - Λ) * q1^2 + of_nat Λ * q2^2"
proof -
  have eq:
    "Lv^2 = of_nat (𝗄 - Λ) * yv^2 + of_nat Λ * y0^2"
    using red by (simp add: algebra_simps)
  show ?thesis
    using eq nz
    by blast
qed

lemma brc_descent_invariant_from_reduced_identity:
  fixes Lv y0 yv :: rat
  assumes red:
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
  assumes nz:
    "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows "brc_descent_invariant m"
  unfolding brc_descent_invariant_def
  using brc_final_rat_from_reduced_identity[OF red nz]
  by blast

definition brc_reduced_identity :: "rat ⇒ rat ⇒ rat ⇒ bool" where
  "brc_reduced_identity Lv y0 yv ⟷
     Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"

lemma brc_descent_invariant_from_reduced_identity_def:
  assumes red: "brc_reduced_identity Lv y0 yv"
  assumes nz: "Lv ≠ 0 ∨ y0 ≠ 0 ∨ yv ≠ 0"
  shows "brc_descent_invariant m"
proof -
  have red':
    "Lv^2 = of_nat Λ * y0^2 + of_nat (𝗄 - Λ) * yv^2"
    using red
    unfolding brc_reduced_identity_def
    by simp
  show ?thesis
    using brc_descent_invariant_from_reduced_identity[OF red' nz]
    by simp
qed

definition brc_y0 :: "rat mat ⇒ nat ⇒ rat" where
  "brc_y0 x w = x_head_sum x w + x_last x w"

definition brc_yv :: "rat mat ⇒ nat ⇒ rat" where
  "brc_yv x w = x_last x w"

definition brc_L :: "rat mat ⇒ nat ⇒ rat" where
  "brc_L x i =
     (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"

lemma brc_x_equation_transformed_named:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
   "(∑i∈{0..<𝗏}. (brc_L x i)^2)
    =
    of_nat Λ * (brc_y0 x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (brc_yv x w)^2"
  using brc_x_equation_transformed[OF v_form abcd, of x]
  unfolding brc_L_def brc_y0_def brc_yv_def
  by simp

lemma brc_reduced_identity_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  shows
    "brc_reduced_identity (brc_L x (𝗏 - 1)) (brc_y0 x w) (brc_yv x w)"
proof -
  have main:
   "(∑i∈{0..<𝗏}. (brc_L x i)^2)
    =
    of_nat Λ * (brc_y0 x w)^2
    +
    y_blocks_sqsum a b c d x w
    +
    of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    using brc_x_equation_transformed_named[OF v_form abcd, of x] .

  have "(brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w
      =
      of_nat Λ * (brc_y0 x w)^2
      +
      y_blocks_sqsum a b c d x w
      +
      of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    using main cancel by simp

  then have "(brc_L x (𝗏 - 1))^2
      =
      of_nat Λ * (brc_y0 x w)^2
      +
      of_nat (𝗄 - Λ) * (brc_yv x w)^2"
    by simp

  then show ?thesis
    unfolding brc_reduced_identity_def
    by simp
qed

lemma brc_v_4w_plus_1_rat_conditional:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have red:
    "brc_reduced_identity (brc_L x (𝗏 - 1)) (brc_y0 x w) (brc_yv x w)"
    using brc_reduced_identity_conditional[OF v_form abcd cancel] .
  show ?thesis
    using brc_descent_invariant_from_reduced_identity_def[OF red nz]
    by simp
qed

lemma brc_v_4w_plus_1_rat_conditional_exists_abcd:
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes cancel:
    "⋀a b c d.
      𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ⟹
      (∑i∈{0..<𝗏}. (brc_L x i)^2)
       =
      (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d :: nat where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    using sum_of_four_squares[of "𝗄 - Λ"]
    by blast

  have cancel':
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
    using cancel[OF abcd] .

  show ?thesis
    using brc_v_4w_plus_1_rat_conditional[OF v_form abcd cancel' nz] .
qed

definition brc_cancel_condition ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_cancel_condition a b c d x w ⟷
     (∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"

lemma brc_v_4w_plus_1_rat_from_cancel_condition:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes cancel: "brc_cancel_condition a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have cancel':
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (brc_L x (𝗏 - 1))^2 + y_blocks_sqsum a b c d x w"
    using cancel
    unfolding brc_cancel_condition_def
    by simp

  show ?thesis
    using brc_v_4w_plus_1_rat_conditional[OF v_form abcd cancel' nz] .
qed

theorem brc_v_4w_plus_1_rat_conditional_final:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes exists_cancel:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_cancel_condition a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and cancel:
    "brc_cancel_condition a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using exists_cancel by blast

  show ?thesis
    using brc_v_4w_plus_1_rat_from_cancel_condition[OF v_form abcd cancel nz] .
qed

lemma brc_cancel_condition_from_indexed_cancel:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes cancel_sum:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
     =
     y_blocks_sqsum a b c d x w"
  shows "brc_cancel_condition a b c d x w"
proof -
  have v_suc: "𝗏 = Suc (4*w)"
    using v_form by simp

  have split:
    "(∑i∈{0..<𝗏}. (brc_L x i)^2)
     =
     (∑i∈{0..<4*w}. (brc_L x i)^2)
     + (brc_L x (4*w))^2"
    using v_suc
    by (simp add: sum.atLeast0_lessThan_Suc)

  have last: "𝗏 - 1 = 4*w"
    using v_form by simp

  show ?thesis
    unfolding brc_cancel_condition_def
    using split cancel_sum last
    by (simp add: algebra_simps)
qed

theorem brc_v_4w_plus_1_rat_from_indexed_cancel:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes exists_indexed_cancel:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and cancel_sum:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using exists_indexed_cancel by blast

  have cancel_cond:
    "brc_cancel_condition a b c d x w"
    using brc_cancel_condition_from_indexed_cancel[
      OF v_form cancel_sum] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_cancel_condition[
      OF v_form abcd cancel_cond nz] .
qed

lemma linear_square_can_be_matched:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
  using choose_y_square_cancel[of e rest]
  by blast

lemma eliminate_one_linear_variable:
  fixes e rest :: rat
  shows "∃y :: rat. (e * y + rest)^2 = y^2"
proof -
  obtain y :: rat where "(e * y + rest)^2 = y^2"
    using choose_y_square_cancel[of e rest] by blast
  then show ?thesis
    by blast
qed

lemma eliminate_list_linear_variables:
  fixes e rest :: "nat ⇒ rat"
  shows "∃y :: nat ⇒ rat.
    ∀i < n. (e i * y i + rest i)^2 = (y i)^2"
proof -
  have "∀i<n. ∃yi :: rat. (e i * yi + rest i)^2 = yi^2"
    using choose_y_square_cancel by blast
  then obtain y where "∀i<n. (e i * y i + rest i)^2 = y i^2"
    by metis
  then show ?thesis
    by blast
qed

lemma eliminate_list_linear_variables_sum:
  fixes e rest :: "nat ⇒ rat"
  shows "∃y :: nat ⇒ rat.
    (∑i∈{0..<n}. (e i * y i + rest i)^2)
    =
    (∑i∈{0..<n}. (y i)^2)"
proof -
  obtain y :: "nat ⇒ rat" where h:
    "∀i < n. (e i * y i + rest i)^2 = (y i)^2"
    using eliminate_list_linear_variables[where n=n and e=e and rest=rest]
    by blast

  have "(∑i∈{0..<n}. (e i * y i + rest i)^2)
      =
        (∑i∈{0..<n}. (y i)^2)"
    using h by simp

  then show ?thesis
    by blast
qed

definition brc_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_elimination_witness a b c d x w ⟷
     (∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"

lemma brc_exists_indexed_cancel_from_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w"
  using witness
  unfolding brc_elimination_witness_def
  by blast

lemma brc_elimination_witness_exists_from_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  using witness .


lemma brc_exists_indexed_cancel:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and elim:
    "brc_elimination_witness a b c d x w"
    and nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using witness by blast

  have cancel:
    "(∑i∈{0..<4*w}. (brc_L x i)^2)
      =
     y_blocks_sqsum a b c d x w"
    using elim
    unfolding brc_elimination_witness_def
    by simp

  show ?thesis
    using abcd cancel nz
    by blast
qed

theorem brc_v_4w_plus_1_rat_from_nonzero_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
  shows "brc_descent_invariant w"
proof -
  have indexed:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       (∑i∈{0..<4*w}. (brc_L x i)^2)
        =
       y_blocks_sqsum a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
    using brc_exists_indexed_cancel[OF v_form witness] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_indexed_cancel[OF v_form indexed] .
qed

definition brc_nonzero_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_nonzero_elimination_witness a b c d x w ⟷
     brc_elimination_witness a b c d x w ∧
     (brc_L x (𝗏 - 1) ≠ 0 ∨
      brc_y0 x w ≠ 0 ∨
      brc_yv x w ≠ 0)"

theorem brc_v_4w_plus_1_rat_from_nonzero_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and wit:
    "brc_nonzero_elimination_witness a b c d x w"
    using witness by blast

  have elim:
    "brc_elimination_witness a b c d x w"
    using wit
    unfolding brc_nonzero_elimination_witness_def
    by simp

  have nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
    using wit
    unfolding brc_nonzero_elimination_witness_def
    by simp

  have witness':
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       (brc_L x (𝗏 - 1) ≠ 0 ∨
        brc_y0 x w ≠ 0 ∨
        brc_yv x w ≠ 0)"
    using abcd elim nz
    by blast

  show ?thesis
    using brc_v_4w_plus_1_rat_from_nonzero_elimination_witness[
      OF v_form witness']
    .
qed

lemma four_sq_nat_coeff_nonzero_rat:
  fixes n :: nat
  assumes "n ≠ 0"
  shows "of_nat n ≠ (0 :: rat)"
  using assms by simp

lemma y_reversible_zero_imp_zero:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes yz: "y_of ((a,b,c,d),(x0,x1,x2,x3)) = (0,0,0,0)"
  shows "x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0"
proof -
  let ?n = "a^2 + b^2 + c^2 + d^2"

  have norm:
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2
     =
     of_nat ?n * (x0^2 + x1^2 + x2^2 + x3^2)"
    using y_norm_identity[of ?n a b c d x0 x1 x2 x3]
    by simp

  have left0:
    "(one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 +
     (four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))))^2 = 0"
    using yz by simp

  have sqsum0:
    "x0^2 + x1^2 + x2^2 + x3^2 = 0"
  proof -
    have "of_nat ?n * (x0^2 + x1^2 + x2^2 + x3^2) = 0"
      using norm left0 by simp
    moreover have "of_nat ?n ≠ (0::rat)"
      using four_sq_nat_coeff_nonzero_rat[of ?n] nzsum
      by blast
    ultimately show ?thesis
      by simp
  qed

  have sqsum_nonneg:
    "0 ≤ x0^2 ∧ 0 ≤ x1^2 ∧ 0 ≤ x2^2 ∧ 0 ≤ x3^2"
    by simp

  have x0sq: "x0^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x1sq: "x1^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x2sq: "x2^2 = 0"
    using sqsum0 sqsum_nonneg by linarith
  have x3sq: "x3^2 = 0"
    using sqsum0 sqsum_nonneg by linarith

  have x0z: "x0 = 0" using x0sq by simp
  have x1z: "x1 = 0" using x1sq by simp
  have x2z: "x2 = 0" using x2sq by simp
  have x3z: "x3 = 0" using x3sq by simp

  show ?thesis
    using x0z x1z x2z x3z by simp
qed

lemma y_reversible_nonzero:
  fixes a b c d :: nat
  fixes x0 x1 x2 x3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes nz: "x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0"
  shows "y_of ((a,b,c,d),(x0,x1,x2,x3)) ≠ (0,0,0,0)"
proof
  assume yz: "y_of ((a,b,c,d),(x0,x1,x2,x3)) = (0,0,0,0)"
  have "x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0"
    using y_reversible_zero_imp_zero[OF nzsum yz] .
  thus False
    using nz by simp
qed

lemma y_block_sqsum_zero_imp_x_block_zero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes z: "y_block_sqsum a b c d x h = 0"
  shows
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
proof -
  let ?Y =
    "y_of ((a,b,c,d),
      (x $$ (4*h,0),
       x $$ (4*h+1,0),
       x $$ (4*h+2,0),
       x $$ (4*h+3,0)))"

  have sum0:
    "(one_of ?Y)^2 + (two_of ?Y)^2 + (three_of ?Y)^2 + (four_of ?Y)^2 = 0"
    using z
    unfolding y_block_sqsum_def
    by simp

  have nonneg:
    "0 ≤ (one_of ?Y)^2 ∧
     0 ≤ (two_of ?Y)^2 ∧
     0 ≤ (three_of ?Y)^2 ∧
     0 ≤ (four_of ?Y)^2"
    by simp

  have y0sq: "(one_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y1sq: "(two_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y2sq: "(three_of ?Y)^2 = 0"
    using sum0 nonneg by linarith
  have y3sq: "(four_of ?Y)^2 = 0"
    using sum0 nonneg by linarith

  have yzero: "?Y = (0,0,0,0)"
    using y0sq y1sq y2sq y3sq
    by (cases ?Y) simp

  show ?thesis
    using y_reversible_zero_imp_zero[OF nzsum yzero]
    by simp
qed

lemma y_block_nonzero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes nz:
    "x $$ (4*h,0) ≠ 0 ∨
     x $$ (4*h+1,0) ≠ 0 ∨
     x $$ (4*h+2,0) ≠ 0 ∨
     x $$ (4*h+3,0) ≠ 0"
  shows "y_block_sqsum a b c d x h ≠ 0"
proof
  assume z: "y_block_sqsum a b c d x h = 0"
  have
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
    using y_block_sqsum_zero_imp_x_block_zero[OF nzsum z] .
  then show False
    using nz by simp
qed

lemma y_blocks_sqsum_zero_imp_x_blocks_zero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes z: "y_blocks_sqsum a b c d x w = 0"
  assumes hw: "h < w"
  shows
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
proof -
  have block0: "y_block_sqsum a b c d x h = 0"
  proof -
    have nonneg: "⋀r. r ∈ {0..<w} ⟹ 0 ≤ y_block_sqsum a b c d x r"
      unfolding y_block_sqsum_def
      by simp
    have "y_blocks_sqsum a b c d x w =
          (∑r∈{0..<w}. y_block_sqsum a b c d x r)"
      unfolding y_blocks_sqsum_def by simp
    then have sum0:
      "(∑r∈{0..<w}. y_block_sqsum a b c d x r) = 0"
      using z by simp
    have "0 ≤ y_block_sqsum a b c d x h"
      using nonneg hw by simp
    moreover have "y_block_sqsum a b c d x h ≤
          (∑r∈{0..<w}. y_block_sqsum a b c d x r)"
    proof -
      have hmem: "h ∈ {0..<w}"
        using hw by simp
      have fin: "finite {0..<w}"
        by simp
      have
        "(∑r∈{0..<w}. y_block_sqsum a b c d x r)
         =
         y_block_sqsum a b c d x h
         +
         (∑r∈{0..<w} - {h}. y_block_sqsum a b c d x r)"
        using sum.remove[OF fin hmem, of "y_block_sqsum a b c d x"]
        by (simp add: algebra_simps)
      moreover have "0 ≤ (∑r∈{0..<w} - {h}. y_block_sqsum a b c d x r)"
      proof (rule sum_nonneg)
        fix r
        assume rmem: "r ∈ {0..<w} - {h}"
        then have "r < w"
          by simp
        then show "0 ≤ y_block_sqsum a b c d x r"
          using nonneg by simp
      qed
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis
      using sum0 by simp
  qed

  show ?thesis
    using y_block_sqsum_zero_imp_x_block_zero[OF nzsum block0] .
qed

lemma x_head_block_nonzero_imp_y_blocks_sqsum_nonzero:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes hw: "h < w"
  assumes nz:
    "x $$ (4*h,0) ≠ 0 ∨
     x $$ (4*h+1,0) ≠ 0 ∨
     x $$ (4*h+2,0) ≠ 0 ∨
     x $$ (4*h+3,0) ≠ 0"
  shows "y_blocks_sqsum a b c d x w ≠ 0"
proof
  assume z: "y_blocks_sqsum a b c d x w = 0"
  have
    "x $$ (4*h,0) = 0 ∧
     x $$ (4*h+1,0) = 0 ∧
     x $$ (4*h+2,0) = 0 ∧
     x $$ (4*h+3,0) = 0"
    using y_blocks_sqsum_zero_imp_x_blocks_zero[OF nzsum z hw] .
  then show False
    using nz by simp
qed

lemma brc_reduced_identity_zero_triple:
  assumes red:
    "brc_reduced_identity Lv y0 yv"
  assumes z:
    "Lv = 0" "y0 = 0" "yv = 0"
  shows True
  using red z
  by simp

lemma brc_nonzero_witnessI:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "brc_nonzero_elimination_witness a b c d x w"
  using elim nz
  unfolding brc_nonzero_elimination_witness_def
  by simp

lemma brc_nonzero_elimination_witness_exists_from_x:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
proof -
  have "brc_nonzero_elimination_witness a b c d x w"
    using brc_nonzero_witnessI[OF elim nz] .
  then show ?thesis
    using abcd by blast
qed

lemma brc_v_4w_plus_1_rat_from_constructed_x:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨
     brc_y0 x w ≠ 0 ∨
     brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_nonzero_elimination_witness a b c d x w"
    using brc_nonzero_elimination_witness_exists_from_x[
      OF v_form abcd elim nz]
    .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_nonzero_witness[OF v_form witness] .
qed

lemma brc_nz_from_x_last_one:
  assumes last_one: "x_last x w = 1"
  shows "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
  unfolding brc_yv_def
  using last_one
  by simp

lemma brc_v_4w_plus_1_rat_from_constructed_x_last_one:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes last_one: "x_last x w = 1"
  shows "brc_descent_invariant w"
proof -
  have nz:
    "brc_L x (𝗏 - 1) ≠ 0 ∨ brc_y0 x w ≠ 0 ∨ brc_yv x w ≠ 0"
    using brc_nz_from_x_last_one[OF last_one] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_constructed_x[
      OF v_form abcd elim nz]
    .
qed

definition brc_last_one_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_last_one_elimination_witness a b c d x w ⟷
     brc_elimination_witness a b c d x w ∧
     x_last x w = 1"

lemma brc_v_4w_plus_1_rat_from_last_one_elimination_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
  shows "brc_descent_invariant w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and wit:
    "brc_last_one_elimination_witness a b c d x w"
    using witness by blast

  have elim:
    "brc_elimination_witness a b c d x w"
    using wit
    unfolding brc_last_one_elimination_witness_def
    by simp

  have last_one:
    "x_last x w = 1"
    using wit
    unfolding brc_last_one_elimination_witness_def
    by simp

  show ?thesis
    using brc_v_4w_plus_1_rat_from_constructed_x_last_one[
      OF v_form abcd elim last_one]
    .
qed

definition brc_blockwise_elimination_witness ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_blockwise_elimination_witness a b c d x w ⟷
     x_last x w = 1 ∧
     (∀h < w.
        (brc_L x (4*h))^2 +
        (brc_L x (4*h + 1))^2 +
        (brc_L x (4*h + 2))^2 +
        (brc_L x (4*h + 3))^2
        =
        y_block_sqsum a b c d x h)"

lemma eliminate_four_linear_variables:
  fixes e0 e1 e2 e3 r0 r1 r2 r3 :: rat
  shows "∃y0 y1 y2 y3 :: rat.
    (e0*y0 + r0)^2 +
    (e1*y1 + r1)^2 +
    (e2*y2 + r2)^2 +
    (e3*y3 + r3)^2
    =
    y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 where y0: "(e0*y0 + r0)^2 = y0^2"
    using choose_y_square_cancel[of e0 r0] by blast
  obtain y1 where y1: "(e1*y1 + r1)^2 = y1^2"
    using choose_y_square_cancel[of e1 r1] by blast
  obtain y2 where y2: "(e2*y2 + r2)^2 = y2^2"
    using choose_y_square_cancel[of e2 r2] by blast
  obtain y3 where y3: "(e3*y3 + r3)^2 = y3^2"
    using choose_y_square_cancel[of e3 r3] by blast
  show ?thesis
  proof
    show "∃y1 y2 y3.
      (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
      (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
      y0^2 + y1^2 + y2^2 + y3^2"
    proof
      show "∃y2 y3.
        (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
        (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
        y0^2 + y1^2 + y2^2 + y3^2"
      proof
        show "∃y3.
          (e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
          (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
          y0^2 + y1^2 + y2^2 + y3^2"
        proof
          show "(e0 * y0 + r0)^2 + (e1 * y1 + r1)^2 +
                (e2 * y2 + r2)^2 + (e3 * y3 + r3)^2 =
                y0^2 + y1^2 + y2^2 + y3^2"
            using y0 y1 y2 y3
            by simp
        qed
      qed
    qed
  qed
qed

definition scale_x :: "rat ⇒ rat mat ⇒ rat mat" where
  "scale_x c x = mat 𝗏 1 (λ(i,j). c * x $$ (i,j))"

lemma scale_x_entry:
  assumes i_lt: "i < 𝗏"
  shows "scale_x c x $$ (i,0) = c * x $$ (i,0)"
  unfolding scale_x_def
  using i_lt
  by simp

lemma brc_L_scale:
  assumes i_lt: "i < 𝗏"
  shows "brc_L (scale_x c x) i = c * brc_L x i"
proof -
  have "brc_L (scale_x c x) i =
        (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * (c * x $$ (h,0)))"
    unfolding brc_L_def
    by (simp add: scale_x_entry)
  also have "... =
        c * (∑h∈{0..<𝗏}. of_int (N $$ (h,i)) * x $$ (h,0))"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis
    unfolding brc_L_def
    by simp
qed

lemma x_last_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "x_last (scale_x c x) w = c * x_last x w"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then show ?thesis
    unfolding x_last_def
    by (simp add: scale_x_entry)
qed

lemma y_block_sqsum_scale:
  assumes h_lt: "h < w"
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "y_block_sqsum a b c d (scale_x r x) h =
         r^2 * y_block_sqsum a b c d x h"
proof -
  have b0: "4*h < 𝗏"
    using h_lt v_form by simp
  have b1: "4*h + 1 < 𝗏"
    using h_lt v_form by simp
  have b2: "4*h + 2 < 𝗏"
    using h_lt v_form by simp
  have b3: "4*h + 3 < 𝗏"
    using h_lt v_form by simp

  show ?thesis
    unfolding y_block_sqsum_def
    using b0 b1 b2 b3
    by (simp add: scale_x_entry power2_eq_square algebra_simps)
qed

lemma y_blocks_sqsum_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "y_blocks_sqsum a b c d (scale_x r x) w =
         r^2 * y_blocks_sqsum a b c d x w"
proof -
  have "⋀h. h ∈ {0..<w} ⟹
        y_block_sqsum a b c d (scale_x r x) h =
        r^2 * y_block_sqsum a b c d x h"
    using y_block_sqsum_scale[OF _ v_form, of _ a b c d r x]
    by simp
  then show ?thesis
    unfolding y_blocks_sqsum_def
    by (simp add: sum_distrib_left)
qed

lemma brc_elimination_witness_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes elim: "brc_elimination_witness a b c d x w"
  shows "brc_elimination_witness a b c d (scale_x r x) w"
proof -
  have left:
    "(∑i∈{0..<4*w}. (brc_L (scale_x r x) i)^2)
     =
     r^2 * (∑i∈{0..<4*w}. (brc_L x i)^2)"
  proof -
    have "⋀i. i ∈ {0..<4*w} ⟹ brc_L (scale_x r x) i = r * brc_L x i"
    proof -
      fix i
      assume i_mem: "i ∈ {0..<4*w}"
      have i_lt_v: "i < 𝗏"
        using i_mem v_form by simp
      show "brc_L (scale_x r x) i = r * brc_L x i"
        using brc_L_scale[OF i_lt_v, of r x] .
    qed
    then show ?thesis
      by (simp add: power2_eq_square sum_distrib_left algebra_simps)
  qed

  have right:
    "y_blocks_sqsum a b c d (scale_x r x) w =
     r^2 * y_blocks_sqsum a b c d x w"
    using y_blocks_sqsum_scale[OF v_form, of a b c d r x] .

  show ?thesis
    using elim left right
    unfolding brc_elimination_witness_def
    by simp
qed

lemma brc_yv_scale:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (scale_x r x) w = r * brc_yv x w"
  unfolding brc_yv_def
  using x_last_scale[OF v_form, of r x]
  by simp

lemma brc_last_one_witness_from_nonzero_yv:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes elim: "brc_elimination_witness a b c d x w"
  assumes nz: "brc_yv x w ≠ 0"
  shows "brc_last_one_elimination_witness a b c d
           (scale_x (1 / brc_yv x w) x) w"
proof -
  have elim_scaled:
    "brc_elimination_witness a b c d
       (scale_x (1 / brc_yv x w) x) w"
    using brc_elimination_witness_scale[OF v_form elim] .

  have last_one:
    "x_last (scale_x (1 / brc_yv x w) x) w = 1"
    using x_last_scale[OF v_form, of "1 / brc_yv x w" x] nz
    unfolding brc_yv_def
    by simp

  show ?thesis
    unfolding brc_last_one_elimination_witness_def
    using elim_scaled last_one
    by simp
qed

lemma brc_last_one_elimination_witness_exists_from_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
proof -
  obtain a b c d x where abcd:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
    and elim:
    "brc_elimination_witness a b c d x w"
    and nz:
    "brc_yv x w ≠ 0"
    using witness by blast

  have last_one:
    "brc_last_one_elimination_witness a b c d
       (scale_x (1 / brc_yv x w) x) w"
    using brc_last_one_witness_from_nonzero_yv[OF v_form elim nz] .

  show ?thesis
    using abcd last_one by blast
qed

lemma brc_v_4w_plus_1_rat_from_yv_nonzero_witness:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
  shows "brc_descent_invariant w"
proof -
  have last_one_witness:
    "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_last_one_elimination_witness a b c d x w"
    using brc_last_one_elimination_witness_exists_from_yv_nonzero[
      OF v_form witness] .

  show ?thesis
    using brc_v_4w_plus_1_rat_from_last_one_elimination_witness[
      OF v_form last_one_witness]
    .
qed

definition last_unit_x :: "nat ⇒ rat mat" where
  "last_unit_x w =
     mat 𝗏 1 (λ(i,j). if j = 0 ∧ i = 4*w then 1 else 0)"

lemma last_unit_x_last:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (last_unit_x w) w = 1"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then show ?thesis
    unfolding brc_yv_def x_last_def last_unit_x_def
    by simp
qed

lemma brc_yv_nonzero_elimination_witness_from_last_unit:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes elim: "brc_elimination_witness a b c d (last_unit_x w) w"
  shows "∃a b c d x.
       𝗄 - Λ = a^2 + b^2 + c^2 + d^2 ∧
       brc_elimination_witness a b c d x w ∧
       brc_yv x w ≠ 0"
proof -
  have yv1: "brc_yv (last_unit_x w) w = 1"
    using last_unit_x_last[OF v_form] .
  then have nz: "brc_yv (last_unit_x w) w ≠ 0"
    by simp
  show ?thesis
    using abcd elim nz
    by blast
qed

lemma brc_elimination_witness_last_unit_conditional:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes abcd: "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  assumes unit_elim:
    "(∑i∈{0..<4*w}. (brc_L (last_unit_x w) i)^2)
     =
     y_blocks_sqsum a b c d (last_unit_x w) w"
  shows "brc_elimination_witness a b c d (last_unit_x w) w"
  using unit_elim
  unfolding brc_elimination_witness_def
  by simp

lemma brc_local_linear_comb_last4:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m i :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes i4: "i ∈ {0..<4}"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
  using linear_comb_of_y_part_2[
    OF four_sq m_v m_gt3 i4
       refl refl refl refl
       x0_y x1_y x2_y x3_y]
  .

lemma brc_local_linear_comb_i0:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
proof -
  have i0: "0 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-0-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i0 x0_y x1_y x2_y x3_y]
    by blast

  have clean:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using clean by blast
qed

lemma brc_local_linear_comb_i1:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
proof -
  have i1: "1 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i1 x0_y x1_y x2_y x3_y]
    by blast

  show ?thesis
  proof -
    have
      "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
      using raw by simp
    then show ?thesis
      by blast
  qed
qed

lemma brc_local_linear_comb_i2:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
proof -
  have i2: "2 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-2-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i2 x0_y x1_y x2_y x3_y]
    by blast

  have target:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using target by blast
qed

lemma brc_local_linear_comb_i3:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃e0 e1 e2 e3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
proof -
  have i3: "3 ∈ {0..<4::nat}"
    by simp

  obtain e0 e1 e2 e3 :: rat where raw:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_last4[
      OF four_sq m_v m_gt3 i3 x0_y x1_y x2_y x3_y]
    by blast

  have target:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e0*y0 + e1*y1 + e2*y2 + e3*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using raw by simp

  show ?thesis
    using target by blast
qed

lemma brc_local_linear_comb_four_exists:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes x0_y:
    "x $$ (m-4,0) = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x1_y:
    "x $$ (m-3,0) = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x2_y:
    "x $$ (m-2,0) = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  assumes x3_y:
    "x $$ (m-1,0) = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃A0 A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
        = A0*y0 + R0 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
        = A1*y1 + R1 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
        = A2*y2 + R2 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
        = A3*y3 + R3"
proof -
  obtain e00 e01 e02 e03 :: rat where eq0:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
      =
      e00*y0 + e01*y1 + e02*y2 + e03*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i0[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e10 e11 e12 e13 :: rat where eq1:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
      =
      e10*y0 + e11*y1 + e12*y2 + e13*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i1[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e20 e21 e22 e23 :: rat where eq2:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
      =
      e20*y0 + e21*y1 + e22*y2 + e23*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i2[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  obtain e30 e31 e32 e33 :: rat where eq3:
    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
      =
      e30*y0 + e31*y1 + e32*y2 + e33*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using brc_local_linear_comb_i3[
      OF four_sq m_v m_gt3 x0_y x1_y x2_y x3_y]
    by blast

  let ?R0 = "e01*y1 + e02*y2 + e03*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
  let ?R1 = "e10*y0 + e12*y2 + e13*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))"
  let ?R2 = "e20*y0 + e21*y1 + e23*y3 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
  let ?R3 = "e30*y0 + e31*y1 + e32*y2 +
      (∑h∈{4..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"

  show ?thesis
  proof
    show "∃A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
        = e00*y0 + R0 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
        = A1*y1 + R1 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
        = A2*y2 + R2 ∧
      (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
        = A3*y3 + R3"
    proof
      show "∃A2 A3 R0 R1 R2 R3 :: rat.
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
          = e00*y0 + R0 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
          = e11*y1 + R1 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
          = A2*y2 + R2 ∧
        (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
          = A3*y3 + R3"
      proof
        show "∃A3 R0 R1 R2 R3 :: rat.
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
            = e00*y0 + R0 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
            = e11*y1 + R1 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
            = e22*y2 + R2 ∧
          (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
            = A3*y3 + R3"
        proof
          show "∃R0 R1 R2 R3 :: rat.
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
              = e00*y0 + R0 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
              = e11*y1 + R1 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
              = e22*y2 + R2 ∧
            (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
              = e33*y3 + R3"
          proof
            show "∃R1 R2 R3 :: rat.
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                = e00*y0 + ?R0 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                = e11*y1 + R1 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                = e22*y2 + R2 ∧
              (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                = e33*y3 + R3"
            proof
              show "∃R2 R3 :: rat.
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                  = e00*y0 + ?R0 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                  = e11*y1 + ?R1 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                  = e22*y2 + R2 ∧
                (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                  = e33*y3 + R3"
              proof
                show "∃R3 :: rat.
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                    = e00*y0 + ?R0 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                    = e11*y1 + ?R1 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                    = e22*y2 + ?R2 ∧
                  (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                    = e33*y3 + R3"
                proof
                  show
                    "(∑h∈{0..<m}. of_int (N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))
                      = e00*y0 + ?R0 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m - Suc (Suc 0))) * x $$ (m-h-1,0))
                      = e11*y1 + ?R1 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))
                      = e22*y2 + ?R2 ∧
                    (∑h∈{0..<m}. of_int (N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))
                      = e33*y3 + ?R3"
                    using eq0 eq1 eq2 eq3
                    by (simp add: algebra_simps)
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma brc_choose_local_y_block:
  fixes A0 A1 A2 A3 R0 R1 R2 R3 :: rat
  shows
    "∃y0 y1 y2 y3 :: rat.
        (A0*y0 + R0)^2 +
        (A1*y1 + R1)^2 +
        (A2*y2 + R2)^2 +
        (A3*y3 + R3)^2
        =
        y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 where y0: "(A0*y0 + R0)^2 = y0^2"
    using choose_y_square_cancel[of A0 R0] by blast
  obtain y1 where y1: "(A1*y1 + R1)^2 = y1^2"
    using choose_y_square_cancel[of A1 R1] by blast
  obtain y2 where y2: "(A2*y2 + R2)^2 = y2^2"
    using choose_y_square_cancel[of A2 R2] by blast
  obtain y3 where y3: "(A3*y3 + R3)^2 = y3^2"
    using choose_y_square_cancel[of A3 R3] by blast

  show ?thesis
  proof
    show "∃y1 y2 y3.
      (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
      (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
      y0^2 + y1^2 + y2^2 + y3^2"
    proof
      show "∃y2 y3.
        (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
        (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
        y0^2 + y1^2 + y2^2 + y3^2"
      proof
        show "∃y3.
          (A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
          (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
          y0^2 + y1^2 + y2^2 + y3^2"
        proof
          show "(A0*y0 + R0)^2 + (A1*y1 + R1)^2 +
                (A2*y2 + R2)^2 + (A3*y3 + R3)^2 =
                y0^2 + y1^2 + y2^2 + y3^2"
            using y0 y1 y2 y3
            by simp
        qed
      qed
    qed
  qed
qed

definition update_x_block ::
  "rat mat ⇒ nat ⇒ rat ⇒ rat ⇒ rat ⇒ rat ⇒ rat mat" where
  "update_x_block x h x0 x1 x2 x3 =
     mat 𝗏 1
       (λ(i,j).
          if j = 0 ∧ i = 4*h then x0
          else if j = 0 ∧ i = 4*h + 1 then x1
          else if j = 0 ∧ i = 4*h + 2 then x2
          else if j = 0 ∧ i = 4*h + 3 then x3
          else x $$ (i,j))"

lemma update_x_block_0:
  assumes "4*h < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) = x0"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_1:
  assumes "4*h + 1 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 1,0) = x1"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_2:
  assumes "4*h + 2 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 2,0) = x2"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_3:
  assumes "4*h + 3 < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (4*h + 3,0) = x3"
  unfolding update_x_block_def
  using assms by simp

lemma update_x_block_preserve_after:
  assumes i_ge: "4 * Suc h ≤ i"
  assumes i_lt: "i < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (i,0) = x $$ (i,0)"
proof -
  have neq0: "i ≠ 4*h"
    using i_ge by auto
  have neq1: "i ≠ 4*h + 1"
    using i_ge by auto
  have neq2: "i ≠ 4*h + 2"
    using i_ge by auto
  have neq3: "i ≠ 4*h + 3"
    using i_ge by auto
  show ?thesis
    unfolding update_x_block_def
    using i_lt neq0 neq1 neq2 neq3
    by simp
qed

lemma update_x_block_preserve_before:
  assumes i_lt_block: "i < 4*h"
  assumes i_lt: "i < 𝗏"
  shows "update_x_block x h x0 x1 x2 x3 $$ (i,0) = x $$ (i,0)"
proof -
  have neq0: "i ≠ 4*h"
    using i_lt_block by auto
  have neq1: "i ≠ 4*h + 1"
    using i_lt_block by auto
  have neq2: "i ≠ 4*h + 2"
    using i_lt_block by auto
  have neq3: "i ≠ 4*h + 3"
    using i_lt_block by auto
  show ?thesis
    unfolding update_x_block_def
    using i_lt neq0 neq1 neq2 neq3
    by simp
qed

lemma update_x_block_y_inv_entries:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "y_of ((a,b,c,d),
      (update_x_block x h x0 x1 x2 x3 $$ (4*h,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0)))
     = (y0,y1,y2,y3)"
proof -
  have entries:
    "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) = x0"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0) = x1"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0) = x2"
    "update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0) = x3"
    using update_x_block_0[OF b0, of x x0 x1 x2 x3]
          update_x_block_1[OF b1, of x x0 x1 x2 x3]
          update_x_block_2[OF b2, of x x0 x1 x2 x3]
          update_x_block_3[OF b3, of x x0 x1 x2 x3]
    by simp_all

  have inv:
    "y_reversible (y_inv_reversible ((a,b,c,d),(y0,y1,y2,y3)))
     = ((a,b,c,d),(y0,y1,y2,y3))"
    using y_inverses_part_2[OF nzsum, of y0 y1 y2 y3] .

  show ?thesis
    using entries inv
    unfolding x0_def x1_def x2_def x3_def
    by simp
qed

lemma y_block_sqsum_update_y_inv:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "y_block_sqsum a b c d
       (update_x_block x h x0 x1 x2 x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have yblock:
    "y_of ((a,b,c,d),
      (update_x_block x h x0 x1 x2 x3 $$ (4*h,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0),
       update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0)))
     = (y0,y1,y2,y3)"
  proof -
    have e0:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h,0) =
       one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_0[OF b0, of x x0 x1 x2 x3]
      unfolding x0_def by simp
    have e1:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+1,0) =
       two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_1[OF b1, of x x0 x1 x2 x3]
      unfolding x1_def by simp
    have e2:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+2,0) =
       three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_2[OF b2, of x x0 x1 x2 x3]
      unfolding x2_def by simp
    have e3:
      "update_x_block x h x0 x1 x2 x3 $$ (4*h+3,0) =
       four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
      using update_x_block_3[OF b3, of x x0 x1 x2 x3]
      unfolding x3_def by simp

    have inv:
      "y_reversible (y_inv_reversible ((a,b,c,d),(y0,y1,y2,y3)))
       = ((a,b,c,d),(y0,y1,y2,y3))"
      using y_inverses_part_2[OF nzsum, of y0 y1 y2 y3] .

    show ?thesis
      using e0 e1 e2 e3 inv
      by simp
  qed

  show ?thesis
    unfolding y_block_sqsum_def
    using yblock
    by simp
qed

lemma y_block_sqsum_update_from_chosen_y:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  shows
    "∃x0 x1 x2 x3 :: rat.
       y_block_sqsum a b c d
         (update_x_block x h x0 x1 x2 x3) h
       =
       y0^2 + y1^2 + y2^2 + y3^2"
proof -
  let ?x0 = "one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x1 = "two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x2 = "three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  let ?x3 = "four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"

  have eq:
    "y_block_sqsum a b c d
       (update_x_block x h ?x0 ?x1 ?x2 ?x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_block_sqsum_update_y_inv[
      OF nzsum b0 b1 b2 b3, of x y0 y1 y2 y3]
    by simp

  show ?thesis
    using eq by blast
qed

lemma brc_local_updated_block_linear_forms:
  fixes a b c d :: nat
  fixes y0 y1 y2 y3 :: rat
  fixes x :: "rat mat"
  fixes m :: nat
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes m_v: "m ≤ 𝗏"
  assumes m_gt3: "3 < m"
  assumes m_block: "m = 4 * Suc h"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  defines "x0 ≡ one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x1 ≡ two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x2 ≡ three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  defines "x3 ≡ four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
  shows
    "∃A0 A1 A2 A3 R0 R1 R2 R3 :: rat.
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-1)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A0*y0 + R0 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m - Suc (Suc 0))) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A1*y1 + R1 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-3)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A2*y2 + R2 ∧
      (∑j∈{0..<m}. of_int (N $$ (m-j-1,m-4)) *
          (update_x_block x h x0 x1 x2 x3) $$ (m-j-1,0))
        = A3*y3 + R3"
proof -
  have e0:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-4,0)
     = one_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_0[OF b0, of x x0 x1 x2 x3]
    unfolding x0_def m_block
    by simp

  have e1:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-3,0)
     = two_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_1[OF b1, of x x0 x1 x2 x3]
    unfolding x1_def m_block
    by simp

  have e2:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-2,0)
     = three_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_2[OF b2, of x x0 x1 x2 x3]
    unfolding x2_def m_block
    by simp

  have e3:
    "(update_x_block x h x0 x1 x2 x3) $$ (m-1,0)
     = four_of (y_inv_of ((a,b,c,d),(y0,y1,y2,y3)))"
    using update_x_block_3[OF b3, of x x0 x1 x2 x3]
    unfolding x3_def m_block
    by (simp add: add.commute)

  show ?thesis
    using brc_local_linear_comb_four_exists[
      OF four_sq m_v m_gt3 e0 e1 e2 e3]
    .
qed

lemma brc_local_block_update_exists:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes h :: nat
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes b0: "4*h < 𝗏"
  assumes b1: "4*h + 1 < 𝗏"
  assumes b2: "4*h + 2 < 𝗏"
  assumes b3: "4*h + 3 < 𝗏"
  shows "∃x' y0 y1 y2 y3.
      y_block_sqsum a b c d x' h =
      y0^2 + y1^2 + y2^2 + y3^2"
proof -
  obtain y0 y1 y2 y3 :: rat where True
    by simp

  obtain x0 x1 x2 x3 :: rat where rhs:
    "y_block_sqsum a b c d
       (update_x_block x h x0 x1 x2 x3) h
     =
     y0^2 + y1^2 + y2^2 + y3^2"
    using y_block_sqsum_update_from_chosen_y[
      OF nzsum b0 b1 b2 b3, of x y0 y1 y2 y3]
    by blast

  then show ?thesis
    by blast
qed

definition brc_start_x :: "nat ⇒ rat mat" where
  "brc_start_x w =
     mat 𝗏 1 (λ(i,j). if j = 0 ∧ i = 4*w then 1 else 0)"

lemma brc_start_x_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (brc_start_x w) w ≠ 0"
proof -
  have "4*w < 𝗏"
    using v_form by simp
  then have "brc_yv (brc_start_x w) w = 1"
    unfolding brc_yv_def x_last_def brc_start_x_def
    by simp
  then show ?thesis
    by simp
qed

lemma last_unit_x_yv_nonzero:
  assumes v_form: "𝗏 = 4 * w + 1"
  shows "brc_yv (last_unit_x w) w ≠ 0"
  using last_unit_x_last[OF v_form]
  by simp

lemma brc_yv_preserved_by_tail_preserve:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes h_lt: "h < w"
  assumes preserve:
    "∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)"
  shows "brc_yv x' w = brc_yv x w"
proof -
  have idx_ge: "4 * Suc h ≤ 4 * w"
    using h_lt by simp
  have idx_lt: "4 * w < 𝗏"
    using v_form by simp
  have "x' $$ (4*w,0) = x $$ (4*w,0)"
    using preserve idx_ge idx_lt by blast
  then show ?thesis
    unfolding brc_yv_def x_last_def
    by simp
qed

lemma brc_apply_local_step_preserves_yv:
  assumes v_form: "𝗏 = 4 * w + 1"
  assumes h_lt: "h < w"
  assumes four_sq: "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes nzsum: "a^2 + b^2 + c^2 + d^2 ≠ 0"
  assumes local_step:
    "⋀x h m.
      m ≤ 𝗏 ⟹
      3 < m ⟹
      m = 4 * Suc h ⟹
      4*h < 𝗏 ⟹
      4*h + 1 < 𝗏 ⟹
      4*h + 2 < 𝗏 ⟹
      4*h + 3 < 𝗏 ⟹
      ∃x'.
        (∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)) ∧
        y_block_sqsum a b c d x' h =
          (∑j∈{0..<4}.
            (∑r∈{0..<4 * Suc h}.
              of_int (N $$ (4 * Suc h-r-1,4 * Suc h-j-1)) *
              x' $$ (4 * Suc h-r-1,0))^2)"
  shows "∃x'. brc_yv x' w = brc_yv x w"
proof -
  let ?m = "4 * Suc h"

  have m_v: "?m ≤ 𝗏"
    using h_lt v_form by simp
  have m_gt3: "3 < ?m"
    by simp
  have b0: "4*h < 𝗏"
    using h_lt v_form by simp
  have b1: "4*h + 1 < 𝗏"
    using h_lt v_form by simp
  have b2: "4*h + 2 < 𝗏"
    using h_lt v_form by simp
  have b3: "4*h + 3 < 𝗏"
    using h_lt v_form by simp

  obtain x' where preserve:
    "∀i. 4 * Suc h ≤ i ⟶ i < 𝗏 ⟶ x' $$ (i,0) = x $$ (i,0)"
    using local_step[OF m_v m_gt3 refl b0 b1 b2 b3]
    by blast

  have "brc_yv x' w = brc_yv x w"
    using brc_yv_preserved_by_tail_preserve[OF v_form h_lt preserve] .

  then show ?thesis
    by blast
qed

definition brc_prefix_eliminated ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ bool" where
  "brc_prefix_eliminated a b c d x q ⟷
     (∀t. t < q ⟶
        y_block_sqsum a b c d x t =
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int (N $$ (4 * Suc t-r-1,4 * Suc t-j-1)) *
            x $$ (4 * Suc t-r-1,0))^2))"

definition brc_prefix_good ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ nat ⇒ nat ⇒ bool" where
  "brc_prefix_good a b c d x q w ⟷
     brc_prefix_eliminated a b c d x q ∧
     (∀h j. h < q ⟶ j < 4 ⟶
        (∑r∈{4 * Suc h..<𝗏}.
          of_int (N $$ (r, 4*h+j)) * x $$ (r,0)) = 0)"

lemma brc_prefix_good_base:
  "brc_prefix_good a b c d x 0 w"
  unfolding brc_prefix_good_def brc_prefix_eliminated_def
  by simp

lemma brc_prefix_eliminated_base:
  "brc_prefix_eliminated a b c d x 0"
  unfolding brc_prefix_eliminated_def
  by simp

lemma brc_prefix_sum_blocks:
  assumes prefix: "brc_prefix_eliminated a b c d x w"
  shows
    "(∑h∈{0..<w}. y_block_sqsum a b c d x h)
     =
     (∑h∈{0..<w}.
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc h}.
            of_int (N $$ (4 * Suc h-r-1,4 * Suc h-j-1)) *
            x $$ (4 * Suc h-r-1,0))^2))"
  using prefix
  unfolding brc_prefix_eliminated_def
  by simp

definition brc_minus_equation :: bool where
  "brc_minus_equation ⟷
    (∃x y z :: rat.
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x^2 = of_nat (𝗄 - Λ) * y^2 - of_nat Λ * z^2)"

lemma brc_minus_from_terminal:
  fixes xv1 y0 yv1 :: rat
  assumes terminal:
    "of_nat (𝗄 - Λ) * xv1^2 =
       of_nat Λ * y0^2 + yv1^2"
  assumes nonzero:
    "xv1 ≠ 0 ∨ y0 ≠ 0 ∨ yv1 ≠ 0"
  shows "brc_minus_equation"
proof -
  have eq:
    "yv1^2 =
       of_nat (𝗄 - Λ) * xv1^2 -
       of_nat Λ * y0^2"
    using terminal
    by linarith

  show ?thesis
    unfolding brc_minus_equation_def
  proof -
    show "∃x y z :: rat.
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      x^2 = of_nat (𝗄 - Λ) * y^2 - of_nat Λ * z^2"
      using eq nonzero
      by blast
  qed
qed

lemma brc_x_equation_extended:
  fixes x :: "rat mat"
  fixes xv1 :: rat
  shows
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         ((∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2)"
proof -
  have base:
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         (∑j ∈ {0..<𝗏}. (x $$ (j,0))^2)"
    using brc_x_equation[of x] .

  show ?thesis
    using base
    by (simp add: algebra_simps)
qed

definition brc_extend_x :: "rat mat ⇒ rat ⇒ rat mat" where
  "brc_extend_x x xv1 =
     mat (𝗏 + 1) 1
       (λ(i,j). if i < 𝗏 then x $$ (i,0) else xv1)"

lemma brc_extend_x_old:
  assumes "i < 𝗏"
  shows "brc_extend_x x xv1 $$ (i,0) = x $$ (i,0)"
  using assms
  unfolding brc_extend_x_def
  by simp

lemma brc_extend_x_last:
  shows "brc_extend_x x xv1 $$ (𝗏,0) = xv1"
  unfolding brc_extend_x_def
  by simp

lemma brc_extend_x_sqsum:
  "(∑i∈{0..<𝗏 + 1}.
      (brc_extend_x x xv1 $$ (i,0))^2)
   =
   (∑i∈{0..<𝗏}. (x $$ (i,0))^2) + xv1^2"
proof -
  have split:
    "{0..<𝗏 + 1} = {0..<𝗏} ∪ {𝗏}"
    by auto

  have disj:
    "{0..<𝗏} ∩ {𝗏} = {}"
    by auto

  have
    "(∑i∈{0..<𝗏 + 1}.
        (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑i∈{0..<𝗏}.
        (brc_extend_x x xv1 $$ (i,0))^2)
       + (brc_extend_x x xv1 $$ (𝗏,0))^2"
    using split disj
    by (simp add: sum.union_disjoint)

  also have
    "... =
     (∑i∈{0..<𝗏}. (x $$ (i,0))^2) + xv1^2"
    using brc_extend_x_old brc_extend_x_last
    by (intro arg_cong2[where f="(+)"]) auto

  finally show ?thesis .
qed

lemma brc_v_plus_one_four_blocks:
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  shows "𝗏 + 1 = 4 * w"
  using v_form w_pos
  by simp

lemma sum_four_blocks:
  fixes f :: "nat ⇒ rat"
  shows
    "(∑i∈{0..<4*w}. f i)
     =
     (∑h∈{0..<w}.
       (f (4*h) + f (4*h+1) + f (4*h+2) + f (4*h+3)))"
proof (induction w)
  case 0
  then show ?case
    by simp
next
  case (Suc w)

  have split:
    "{0..<4 * Suc w} =
     {0..<4*w} ∪ {4*w, 4*w+1, 4*w+2, 4*w+3}"
    by auto

  have disj:
    "{0..<4*w} ∩ {4*w, 4*w+1, 4*w+2, 4*w+3} = {}"
    by auto

  show ?case
    unfolding split
    using disj Suc.IH
    by (simp add: sum.union_disjoint algebra_simps)
qed

lemma brc_x_equation_extended_vector:
  fixes x :: "rat mat"
  fixes xv1 :: rat
  shows
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         (∑j ∈ {0..<𝗏 + 1}.
            (brc_extend_x x xv1 $$ (j,0))^2)"
proof -
  have ext:
    "(∑j ∈ {0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (j,0))^2)
     =
     (∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2"
    using brc_extend_x_sqsum[of x xv1] .

  have base:
    "(∑i ∈ {0..<𝗏}.
       (∑h ∈ {0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_int (int (𝗄 - Λ)) * xv1^2
     =
       of_int (int Λ) *
         (∑j ∈ {0..<𝗏}. x $$ (j,0))^2
       + of_int (int (𝗄 - Λ)) *
         ((∑j ∈ {0..<𝗏}. (x $$ (j,0))^2) + xv1^2)"
    using brc_x_equation_extended[of x xv1] .

  show ?thesis
    using base ext
    by simp
qed

lemma brc_extend_x_sqsum_blocks:
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  shows
    "(∑i∈{0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
       ((brc_extend_x x xv1 $$ (4*h,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
proof -
  have size:
    "𝗏 + 1 = 4 * w"
    using brc_v_plus_one_four_blocks[OF v_form w_pos] .

  have blocks:
    "(∑i∈{0..<4*w}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
       ((brc_extend_x x xv1 $$ (4*h,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
        (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
    using sum_four_blocks[
      of "λi. (brc_extend_x x xv1 $$ (i,0))^2" w] .

  from blocks show ?thesis
    using size
    by simp
qed

lemma brc_extend_x_transformed_blocks:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  assumes four_sq:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "of_nat (𝗄 - Λ) *
       (∑i∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)"
proof -
  have blocks:
    "(∑i∈{0..<𝗏 + 1}.
       (brc_extend_x x xv1 $$ (i,0))^2)
     =
     (∑h∈{0..<w}.
        x_block_sqsum (brc_extend_x x xv1) h)"
  proof -
    have split:
      "(∑i∈{0..<𝗏 + 1}.
         (brc_extend_x x xv1 $$ (i,0))^2)
       =
       (∑h∈{0..<w}.
         ((brc_extend_x x xv1 $$ (4*h,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+1,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+2,0))^2 +
          (brc_extend_x x xv1 $$ (4*h+3,0))^2))"
      using brc_extend_x_sqsum_blocks[
        OF v_form w_pos, of x xv1] .

    show ?thesis
      using split
      unfolding x_block_sqsum_def
      by simp
  qed

  have block_transform:
    "⋀h. h ∈ {0..<w} ⟹
       of_nat (𝗄 - Λ) *
         x_block_sqsum (brc_extend_x x xv1) h
       =
       y_block_sqsum a b c d
         (brc_extend_x x xv1) h"
    using y_block_sqsum_identity[
      OF four_sq, of "brc_extend_x x xv1"]
    by simp

  have
    "of_nat (𝗄 - Λ) *
       (∑i∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (i,0))^2)
     =
     of_nat (𝗄 - Λ) *
       (∑h∈{0..<w}.
          x_block_sqsum (brc_extend_x x xv1) h)"
    using blocks
    by simp

  also have
    "... =
     (∑h∈{0..<w}.
        of_nat (𝗄 - Λ) *
          x_block_sqsum (brc_extend_x x xv1) h)"
    by (simp add: sum_distrib_left)

  also have
    "... =
     (∑h∈{0..<w}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)"
    using block_transform
    by simp

  finally show ?thesis .
qed

lemma brc_x_equation_minus_transformed:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes xv1 :: rat
  assumes v_form: "𝗏 = 4 * w - 1"
  assumes w_pos: "0 < w"
  assumes four_sq:
    "𝗄 - Λ = a^2 + b^2 + c^2 + d^2"
  shows
    "(∑i∈{0..<𝗏}.
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_nat (𝗄 - Λ) * xv1^2
     =
       of_nat Λ *
         (∑j∈{0..<𝗏}. x $$ (j,0))^2
       +
       (∑h∈{0..<w}.
          y_block_sqsum a b c d
            (brc_extend_x x xv1) h)"
proof -
  have base:
    "(∑i∈{0..<𝗏}.
       (∑h∈{0..<𝗏}.
          of_int (N $$ (h,i)) * x $$ (h,0))^2)
       + of_nat (𝗄 - Λ) * xv1^2
     =
       of_nat Λ *
         (∑j∈{0..<𝗏}. x $$ (j,0))^2
       +
       of_nat (𝗄 - Λ) *
         (∑j∈{0..<𝗏 + 1}.
            (brc_extend_x x xv1 $$ (j,0))^2)"
    using brc_x_equation_extended_vector[of x xv1]
    by simp

  have transformed:
    "of_nat (𝗄 - Λ) *
       (∑j∈{0..<𝗏 + 1}.
          (brc_extend_x x xv1 $$ (j,0))^2)
     =
       (∑h∈{0..<w}.
          y_block_sqsum a b c d
            (brc_extend_x x xv1) h)"
    using brc_extend_x_transformed_blocks[
      OF v_form w_pos four_sq, of x xv1] .

  show ?thesis
    using base transformed
    by simp
qed

definition brc_minus_prefix_eliminated ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_prefix_eliminated a b c d x xv1 q ⟷
     (∀t. t < q ⟶
        y_block_sqsum a b c d (brc_extend_x x xv1) t =
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x xv1 $$ (4 * Suc t-r-1,0))^2))"

definition brc_minus_prefix_good ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat mat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_prefix_good a b c d x xv1 q ⟷
     brc_minus_prefix_eliminated a b c d x xv1 q ∧
     (∀h j. h < q ⟶ j < 4 ⟶
        (∑r∈{4 * Suc h..<𝗏}.
          of_int (N $$ (r,4*h+j)) * x $$ (r,0)) = 0)"

lemma brc_minus_prefix_eliminated_base:
  "brc_minus_prefix_eliminated a b c d x xv1 0"
  unfolding brc_minus_prefix_eliminated_def
  by simp

lemma brc_minus_prefix_good_base:
  "brc_minus_prefix_good a b c d x xv1 0"
  unfolding brc_minus_prefix_good_def
  using brc_minus_prefix_eliminated_base
  by simp

lemma brc_minus_prefix_sum_blocks:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  shows
    "(∑h∈{0..<q}.
        y_block_sqsum a b c d
          (brc_extend_x x xv1) h)
     =
     (∑h∈{0..<q}.
        (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc h}.
            of_int
              (N $$ (4 * Suc h-r-1,
                      4 * Suc h-j-1)) *
            brc_extend_x x xv1 $$
              (4 * Suc h-r-1,0))^2))"
  using prefix
  unfolding brc_minus_prefix_eliminated_def
  by simp

lemma brc_minus_prefix_eliminated_step:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  assumes before:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
       x' $$ (i,0) = x $$ (i,0)"
  assumes local:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc q}.
         of_int
           (N $$ (4 * Suc q-r-1,
                   4 * Suc q-j-1)) *
         brc_extend_x x' xv1 $$
           (4 * Suc q-r-1,0))^2)"
  shows
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc q)"
proof -
  show ?thesis
    unfolding brc_minus_prefix_eliminated_def
  proof (intro allI impI)
    fix t
    assume t_lt: "t < Suc q"

    show
      "y_block_sqsum a b c d
         (brc_extend_x x' xv1) t
       =
       (∑j∈{0..<4}.
         (∑r∈{0..<4 * Suc t}.
           of_int
             (N $$ (4 * Suc t-r-1,
                     4 * Suc t-j-1)) *
           brc_extend_x x' xv1 $$
             (4 * Suc t-r-1,0))^2)"
    proof (cases "t < q")
      case True

      have block_bound:
        "4 * Suc t ≤ 4 * q"
        using True
        by simp

      have agree:
        "⋀i. i < 4 * Suc t ⟹
          brc_extend_x x' xv1 $$ (i,0) =
          brc_extend_x x xv1 $$ (i,0)"
      proof -
        fix i
        assume i_lt: "i < 4 * Suc t"

        have i_lt_4q:
          "i < 4*q"
          using i_lt block_bound
          by simp

        have i_lt_v:
          "i < 𝗏"
          using i_lt_4q q_bound
          by simp

        have xx:
          "x' $$ (i,0) = x $$ (i,0)"
          using before i_lt_4q i_lt_v
          by blast

        show
          "brc_extend_x x' xv1 $$ (i,0) =
           brc_extend_x x xv1 $$ (i,0)"
          using xx i_lt_v
          unfolding brc_extend_x_def
          by simp
      qed

      have old_block:
        "y_block_sqsum a b c d
           (brc_extend_x x' xv1) t
         =
         y_block_sqsum a b c d
           (brc_extend_x x xv1) t"
        unfolding y_block_sqsum_def
        using agree
        by simp

      have old_rhs:
        "(∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x' xv1 $$
              (4 * Suc t-r-1,0))^2)
         =
         (∑j∈{0..<4}.
          (∑r∈{0..<4 * Suc t}.
            of_int
              (N $$ (4 * Suc t-r-1,
                      4 * Suc t-j-1)) *
            brc_extend_x x xv1 $$
              (4 * Suc t-r-1,0))^2)"
      proof -
        have index_bound:
          "⋀r. r ∈ {0..<4 * Suc t} ⟹
             4 * Suc t-r-1 < 4 * Suc t"
          by simp

        show ?thesis
          using agree index_bound
          by (intro sum.cong) auto
      qed

      have old:
        "y_block_sqsum a b c d
           (brc_extend_x x xv1) t
         =
         (∑j∈{0..<4}.
           (∑r∈{0..<4 * Suc t}.
             of_int
               (N $$ (4 * Suc t-r-1,
                       4 * Suc t-j-1)) *
             brc_extend_x x xv1 $$
               (4 * Suc t-r-1,0))^2)"
        using prefix True
        unfolding brc_minus_prefix_eliminated_def
        by blast

      show ?thesis
        using old_block old_rhs old
        by simp
    next
      case False

      have tq:
        "t = q"
        using t_lt False
        by simp

      show ?thesis
        using local
        unfolding tq
        by simp
    qed
  qed
qed

definition brc_minus_local_step ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat ⇒ nat ⇒ bool" where
  "brc_minus_local_step a b c d xv1 q ⟷
     (∀x :: rat mat.
       4 * q ≤ 𝗏 ⟶
       (∃x' :: rat mat.
          (∀i. i < 4*q ⟶ i < 𝗏 ⟶
               x' $$ (i,0) = x $$ (i,0)) ∧
          y_block_sqsum a b c d
            (brc_extend_x x' xv1) q
          =
          (∑j∈{0..<4}.
            (∑r∈{0..<4 * Suc q}.
              of_int
                (N $$ (4 * Suc q-r-1,
                        4 * Suc q-j-1)) *
              brc_extend_x x' xv1 $$
                (4 * Suc q-r-1,0))^2)))"

lemma brc_minus_prefix_step_exists:
  assumes prefix:
    "brc_minus_prefix_eliminated a b c d x xv1 q"
  assumes q_bound:
    "4 * q ≤ 𝗏"
  assumes step:
    "brc_minus_local_step a b c d xv1 q"
  shows
    "∃x'.
       brc_minus_prefix_eliminated
         a b c d x' xv1 (Suc q)"
proof -
  obtain x' where before:
    "∀i. i < 4*q ⟶ i < 𝗏 ⟶
         x' $$ (i,0) = x $$ (i,0)"
    and local:
    "y_block_sqsum a b c d
       (brc_extend_x x' xv1) q
     =
     (∑j∈{0..<4}.
       (∑r∈{0..<4 * Suc q}.
         of_int
           (N $$ (4 * Suc q-r-1,
                   4 * Suc q-j-1)) *
         brc_extend_x x' xv1 $$
           (4 * Suc q-r-1,0))^2)"
    using step q_bound
    unfolding brc_minus_local_step_def
    by blast

  have
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc q)"
    using brc_minus_prefix_eliminated_step[
      OF prefix q_bound before local] .

  then show ?thesis
    by blast
qed

lemma brc_minus_prefix_exists_upto:
  assumes steps:
    "∀q<Q. brc_minus_local_step a b c d xv1 q"
  assumes bound:
    "4 * Q ≤ 𝗏"
  shows
    "∃x :: rat mat.
       brc_minus_prefix_eliminated
         a b c d x xv1 Q"
  using steps bound
proof (induction Q)
  case 0

  show ?case
    using brc_minus_prefix_eliminated_base
    by blast
next
  case (Suc Q)

  have steps_Q:
    "∀q<Q. brc_minus_local_step a b c d xv1 q"
    using Suc.prems(1)
    by simp

  have bound_Q:
    "4 * Q ≤ 𝗏"
    using Suc.prems(2)
    by simp

  obtain x :: "rat mat" where prefix:
    "brc_minus_prefix_eliminated
       a b c d x xv1 Q"
    using Suc.IH[OF steps_Q bound_Q]
    by blast

  have local_Q:
    "brc_minus_local_step a b c d xv1 Q"
    using Suc.prems(1)
    by simp

  obtain x' :: "rat mat" where next_prefix:
    "brc_minus_prefix_eliminated
       a b c d x' xv1 (Suc Q)"
    using brc_minus_prefix_step_exists[
      OF prefix bound_Q local_Q]
    by blast

  show ?case
    using next_prefix
    by blast
qed

lemma choose_y_linear_square:
  fixes A R :: rat
  shows "∃y :: rat. (A*y + R)^2 = y^2"
proof (cases "A = 1")
  case True

  have exists_y:
    "∃y :: rat. 2 * y = -R"
  proof
    show "2 * (-R / 2) = -R"
      by simp
  qed

  obtain y :: rat where hy:
    "2 * y = -R"
    using exists_y
    by blast

  have linear:
    "A * y + R = -y"
    using True hy
    by (simp add: algebra_simps)

  have square:
    "(A * y + R)^2 = y^2"
    using linear
    by simp

  show ?thesis
    using square
    by blast
next
  case False

  have denom:
    "1 - A ≠ 0"
    using False
    by simp

  have exists_y:
    "∃y :: rat. (1 - A) * y = R"
  proof
    show "(1 - A) * (R / (1 - A)) = R"
      using denom
      by simp
  qed

  obtain y :: rat where hy:
    "(1 - A) * y = R"
    using exists_y
    by blast

  have linear:
    "A * y + R = y"
    using hy
    by (simp add: algebra_simps)

  have square:
    "(A * y + R)^2 = y^2"
    using linear
    by simp

  show ?thesis
    using square
    by blast
qed

definition brc_linear_coeff ::
  "nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ nat ⇒ rat" where
  "brc_linear_coeff a b c d m i j =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
     if j = 0 then
       of_int (N $$ (m-4,m-i-1)) * of_nat a / D +
       of_int (N $$ (m-3,m-i-1)) * of_nat b / D +
       of_int (N $$ (m-2,m-i-1)) * of_nat c / D +
       of_int (N $$ (m-1,m-i-1)) * of_nat d / D
     else if j = 1 then
       - of_int (N $$ (m-4,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-2,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat c / D
     else if j = 2 then
       - of_int (N $$ (m-4,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-1,m-i-1)) * of_nat b / D
     else
       - of_int (N $$ (m-4,m-i-1)) * of_nat d / D -
         of_int (N $$ (m-3,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat a / D)"

lemma brc_linear_coeff_0:
  "brc_linear_coeff a b c d m i 0 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       of_int (N $$ (m-4,m-i-1)) * of_nat a / D +
       of_int (N $$ (m-3,m-i-1)) * of_nat b / D +
       of_int (N $$ (m-2,m-i-1)) * of_nat c / D +
       of_int (N $$ (m-1,m-i-1)) * of_nat d / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_1:
  "brc_linear_coeff a b c d m i 1 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-2,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat c / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_2:
  "brc_linear_coeff a b c d m i 2 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-3,m-i-1)) * of_nat d / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat a / D -
         of_int (N $$ (m-1,m-i-1)) * of_nat b / D)"
  unfolding brc_linear_coeff_def
  by simp

lemma brc_linear_coeff_3:
  "brc_linear_coeff a b c d m i 3 =
    (let D = of_nat (a^2 + b^2 + c^2 + d^2) :: rat in
       - of_int (N $$ (m-4,m-i-1)) * of_nat d / D -
         of_int (N $$ (m-3,m-i-1)) * of_nat c / D +
         of_int (N $$ (m-2,m-i-1)) * of_nat b / D +
         of_int (N $$ (m-1,m-i-1)) * of_nat a / D)"
  unfolding brc_linear_coeff_def
  by simp

definition brc_linear_tail ::
  "rat mat ⇒ nat ⇒ nat ⇒ rat" where
  "brc_linear_tail x m i =
    (∑h∈{4..<m}.
       of_int (N $$ (m-h-1,m-i-1)) *
       x $$ (m-h-1,0))"

lemma linear_comb_of_y_explicit:
  fixes a b c d :: nat
  fixes x :: "rat mat"
  fixes x0 x1 x2 x3 :: rat
  fixes i m :: nat
  assumes four_sq:
    "a^2 + b^2 + c^2 + d^2 = 𝗄 - Λ"
  assumes m_v:
    "m ≤ 𝗏"
  assumes m_gt3:
    "3 < m"
  assumes i4:
    "i ∈ {0..<4}"
  assumes x0_def:
    "x0 = x $$ (m - 4, 0)"
  assumes x1_def:
    "x1 = x $$ (m - 3, 0)"
  assumes x2_def:
    "x2 = x $$ (m - 2, 0)"
  assumes x3_def:
    "x3 = x $$ (m - 1, 0)"
  shows
    "(∑h∈{0..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       brc_linear_coeff a b c d m i 0 *
         one_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 1 *
         two_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 2 *
         three_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_coeff a b c d m i 3 *
         four_of (y_of ((a,b,c,d),(x0,x1,x2,x3))) +
       brc_linear_tail x m i"
proof -
  let ?D =
    "of_nat (a^2 + b^2 + c^2 + d^2) :: rat"

  let ?y0 =
    "one_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y1 =
    "two_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y2 =
    "three_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  let ?y3 =
    "four_of (y_of ((a,b,c,d),(x0,x1,x2,x3)))"

  have nz:
    "a^2 + b^2 + c^2 + d^2 ≠ 0"
  proof -
    have diff_pos:
      "0 < 𝗄 - Λ"
      using blocksize_gt_index
      by simp

    show ?thesis
      using four_sq diff_pos
      by simp
  qed

  have key:
    "y_inv_reversible
       (y_reversible ((a,b,c,d),(x0,x1,x2,x3)))
     =
     ((a,b,c,d),(x0,x1,x2,x3))"
    using y_inverses_part_1[OF nz, of x0 x1 x2 x3] .

  have x0_inv:
    "x0 =
       (of_nat a * ?y0 -
        of_nat b * ?y1 -
        of_nat c * ?y2 -
        of_nat d * ?y3) / ?D"
    using key
    by simp

  have x1_inv:
    "x1 =
       (of_nat b * ?y0 +
        of_nat a * ?y1 +
        of_nat d * ?y2 -
        of_nat c * ?y3) / ?D"
    using key
    by simp

  have x2_raw:
    "x2 =
       (of_nat c * ?y0 +
        of_nat a * ?y2 +
        of_nat b * ?y3 -
        of_nat d * ?y1) / ?D"
    using key
    by simp

  have x2_inv:
    "x2 =
       (of_nat c * ?y0 -
        of_nat d * ?y1 +
        of_nat a * ?y2 +
        of_nat b * ?y3) / ?D"
    using x2_raw
    by (simp add: algebra_simps)

  have x3_raw:
    "x3 =
       (of_nat d * ?y0 +
        of_nat c * ?y1 +
        of_nat a * ?y3 -
        of_nat b * ?y2) / ?D"
    using key
    by simp

  have x3_inv:
    "x3 =
       (of_nat d * ?y0 +
        of_nat c * ?y1 -
        of_nat b * ?y2 +
        of_nat a * ?y3) / ?D"
    using x3_raw
    by (simp add: algebra_simps)

  have interval_split:
    "{0..<m} = {0..<4} ∪ {4..<m}"
    using m_gt3
    by auto

  have interval_disjoint:
    "{0..<4} ∩ {4..<m} = {}"
    by auto

  have sum_split:
    "(∑h∈{0..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
     (∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     +
     (∑h∈{4..<m}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))"
    using interval_split interval_disjoint
    by (simp add: sum.union_disjoint)

  have first_four:
    "(∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       of_int (N $$ (m - 4, m - i - 1)) * x0 +
       of_int (N $$ (m - 3, m - i - 1)) * x1 +
       of_int (N $$ (m - 2, m - i - 1)) * x2 +
       of_int (N $$ (m - 1, m - i - 1)) * x3"
    using x0_def x1_def x2_def x3_def m_gt3
    by (simp add: numeral.simps(2,3) algebra_simps)

  have expanded:
    "(∑h∈{0..<4}.
       of_int (N $$ (m - h - 1, m - i - 1)) *
       x $$ (m - h - 1, 0))
     =
       brc_linear_coeff a b c d m i 0 * ?y0 +
       brc_linear_coeff a b c d m i 1 * ?y1 +
       brc_linear_coeff a b c d m i 2 * ?y2 +
       brc_linear_coeff a b c d m i 3 * ?y3"
  proof -
    have
      "(∑h∈{0..<4}.
         of_int (N $$ (m - h - 1, m - i - 1)) *
         x $$ (m - h - 1, 0))
       =
         of_int (N $$ (m - 4, m - i - 1)) * x0 +
         of_int (N $$ (m - 3, m - i - 1)) * x1 +
         of_int (N $$ (m - 2, m - i - 1)) * x2 +
         of_int (N $$ (m - 1, m - i - 1)) * x3"
      using first_four .

    also have
      "... =
       of_int (N $$ (m - 4, m - i - 1)) *
         ((of_nat a * ?y0 -
           of_nat b * ?y1 -
           of_nat c * ?y2 -
           of_nat d * ?y3) / ?D) +
       of_int (N $$ (m - 3, m - i - 1)) *
         ((of_nat b * ?y0 +
           of_nat a * ?y1 +
           of_nat d * ?y2 -
           of_nat c * ?y3) / ?D) +
       of_int (N $$ (m - 2, m - i - 1)) *
         ((of_nat c * ?y0 -
           of_nat d * ?y1 +
           of_nat a * ?y2 +
           of_nat b * ?y3) / ?D) +
       of_int (N $$ (m - 1, m - i - 1)) *
         ((of_nat d * ?y0 +
           of_nat c * ?y1 -
           of_nat b * ?y2 +
           of_nat a * ?y3) / ?D)"
      using x0_inv x1_inv x2_inv x3_inv
      by simp

    also have
      "... =
       brc_linear_coeff a b c d m i 0 * ?y0 +
       brc_linear_coeff a b c d m i 1 * ?y1 +
       brc_linear_coeff a b c d m i 2 * ?y2 +
       brc_linear_coeff a b c d m i 3 * ?y3"
    proof -
      let ?A0 = "of_int (N $$ (m-4, m-i-1)) :: rat"
      let ?A1 = "of_int (N $$ (m-3, m-i-1)) :: rat"
      let ?A2 = "of_int (N $$ (m-2, m-i-1)) :: rat"
      let ?A3 = "of_int (N $$ (m-1, m-i-1)) :: rat"

      have part0:
        "?A0 *
           ((of_nat a * ?y0 -
             of_nat b * ?y1 -
             of_nat c * ?y2 -
             of_nat d * ?y3) / ?D)
         =
           (?A0 * of_nat a / ?D) * ?y0 -
           (?A0 * of_nat b / ?D) * ?y1 -
           (?A0 * of_nat c / ?D) * ?y2 -
           (?A0 * of_nat d / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part1:
        "?A1 *
           ((of_nat b * ?y0 +
             of_nat a * ?y1 +
             of_nat d * ?y2 -
             of_nat c * ?y3) / ?D)
         =
           (?A1 * of_nat b / ?D) * ?y0 +
           (?A1 * of_nat a / ?D) * ?y1 +
           (?A1 * of_nat d / ?D) * ?y2 -
           (?A1 * of_nat c / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part2:
        "?A2 *
           ((of_nat c * ?y0 -
             of_nat d * ?y1 +
             of_nat a * ?y2 +
             of_nat b * ?y3) / ?D)
         =
           (?A2 * of_nat c / ?D) * ?y0 -
           (?A2 * of_nat d / ?D) * ?y1 +
           (?A2 * of_nat a / ?D) * ?y2 +
           (?A2 * of_nat b / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have part3:
        "?A3 *
           ((of_nat d * ?y0 +
             of_nat c * ?y1 -
             of_nat b * ?y2 +
             of_nat a * ?y3) / ?D)
         =
           (?A3 * of_nat d / ?D) * ?y0 +
           (?A3 * of_nat c / ?D) * ?y1 -
           (?A3 * of_nat b / ?D) * ?y2 +
           (?A3 * of_nat a / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left
            distrib_right
            minus_mult_left
            minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group0:
        "(?A0 * of_nat a / ?D +
          ?A1 * of_nat b / ?D +
          ?A2 * of_nat c / ?D +
          ?A3 * of_nat d / ?D) * ?y0
         =
          (?A0 * of_nat a / ?D) * ?y0 +
          (?A1 * of_nat b / ?D) * ?y0 +
          (?A2 * of_nat c / ?D) * ?y0 +
          (?A3 * of_nat d / ?D) * ?y0"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group1:
        "(- ?A0 * of_nat b / ?D +
            ?A1 * of_nat a / ?D -
            ?A2 * of_nat d / ?D +
            ?A3 * of_nat c / ?D) * ?y1
         =
          - (?A0 * of_nat b / ?D) * ?y1 +
            (?A1 * of_nat a / ?D) * ?y1 -
            (?A2 * of_nat d / ?D) * ?y1 +
            (?A3 * of_nat c / ?D) * ?y1"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group2:
        "(- ?A0 * of_nat c / ?D +
            ?A1 * of_nat d / ?D +
            ?A2 * of_nat a / ?D -
            ?A3 * of_nat b / ?D) * ?y2
         =
          - (?A0 * of_nat c / ?D) * ?y2 +
            (?A1 * of_nat d / ?D) * ?y2 +
            (?A2 * of_nat a / ?D) * ?y2 -
            (?A3 * of_nat b / ?D) * ?y2"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have group3:
        "(- ?A0 * of_nat d / ?D -
            ?A1 * of_nat c / ?D +
            ?A2 * of_nat b / ?D +
            ?A3 * of_nat a / ?D) * ?y3
         =
          - (?A0 * of_nat d / ?D) * ?y3 -
            (?A1 * of_nat c / ?D) * ?y3 +
            (?A2 * of_nat b / ?D) * ?y3 +
            (?A3 * of_nat a / ?D) * ?y3"
        by (simp only:
            divide_inverse
            diff_conv_add_uminus
            distrib_left distrib_right
            minus_mult_left minus_mult_right
            mult.assoc mult.commute mult.left_commute
            add.assoc add.commute add.left_commute)

      have combined:
        "?A0 *
           ((of_nat a * ?y0 -
             of_nat b * ?y1 -
             of_nat c * ?y2 -
             of_nat d * ?y3) / ?D) +
         ?A1 *
           ((of_nat b * ?y0 +
             of_nat a * ?y1 +
             of_nat d * ?y2 -
             of_nat c * ?y3) / ?D) +
         ?A2 *
           ((of_nat c * ?y0 -
             of_nat d * ?y1 +
             of_nat a * ?y2 +
             of_nat b * ?y3) / ?D) +
         ?A3 *
           ((of_nat d * ?y0 +
             of_nat c * ?y1 -
             of_nat b * ?y2 +
             of_nat a * ?y3) / ?D)
         =
         (?A0 * of_nat a / ?D +
          ?A1 * of_nat b / ?D +
          ?A2 * of_nat c / ?D +
          ?A3 * of_nat d / ?D) * ?y0 +
         (- ?A0 * of_nat b / ?D +
            ?A1 * of_nat a / ?D -
            ?A2 * of_nat d / ?D +
            ?A3 * of_nat c / ?D) * ?y1 +
         (- ?A0 * of_nat c / ?D +
            ?A1 * of_nat d / ?D +
            ?A2 * of_nat a / ?D -
            ?A3 * of_nat b / ?D) * ?y2 +
         (- ?A0 * of_nat d / ?D -
            ?A1 * of_nat c / ?D +
            ?A2 * of_nat b / ?D +
            ?A3 * of_nat a / ?D) * ?y3"
        apply (subst part0)
        apply (subst part1)
        apply (subst part2)
        apply (subst part3)
        apply (subst group0)
        apply (subst group1)
        apply (subst group2)
        apply (subst group3)
        by (simp only:
            diff_conv_add_uminus
            minus_mult_left
            minus_mult_right
            add.assoc add.commute add.left_commute)

      show ?thesis
        using combined
        by (simp only:
            brc_linear_coeff_0
            brc_linear_coeff_1
            brc_linear_coeff_2
            brc_linear_coeff_3
            Let_def)
    qed

    finally show ?thesis .
  qed

  show ?thesis
    using sum_split expanded
    unfolding brc_linear_tail_def
    by simp
qed

end
end
