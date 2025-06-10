(* Title: Bruck_Ryser_Chowla
   Author: Craig Alan Feinstein
*)

theory Bruck_Ryser_Chowla imports
  Fishers_Inequality.Fishers_Inequality SumSquares.FourSquares Pell.Pell 
  Van_der_Waerden.Digits

begin 

section \<open>Bruck Ryser Chowla Theorem\<close>
text \<open>The Bruck Ryser Chowla Theorem states the following:
Let $(v,k,\Lambda)$ be a symmetric BIBD. If v is even, 
then $k-\Lambda$ will be a perfect square. And if v is odd,
then there will exist integers $(x,y,z) \neq (0,0,0)$ such that
$x^2 = (k-\<Lambda>) y^2 = (-1)^{(v-1)/2}\<Lambda>z^2$. The proof comes from 
"Combinatorial Designs: Constructions and Analysis" by Douglas R.
Stinson.\<close>

context ordered_sym_bibd
begin

subsection \<open>v is even\<close>

lemma apply_nec_cond_one_1: shows "\<k> * (\<k> - 1) = \<Lambda> * (\<v> - 1)"
proof -
  have "\<r> = \<k>" using rep_value_sym by simp
    moreover have "\<r> * (\<k> - 1) = \<Lambda> * (\<v> - 1)"
     using necessary_condition_one by simp
      ultimately show "\<k> * (\<k> - 1) = \<Lambda> * (\<v> - 1)" by simp
    qed

lemma apply_nec_cond_one_2: shows "\<k> + \<Lambda> * (\<v> - 1) = \<k>^2"
proof -
  have "\<k> + \<Lambda> * (\<v> - 1) = \<k> + \<k> * (\<k> - 1)"
    using apply_nec_cond_one_1 by simp
    also have "\<k> + \<k> * (\<k> - 1) = \<k>^2"
      by (simp add: algebra_simps power2_eq_square)
    ultimately show "\<k> + \<Lambda> * (\<v> - 1) = \<k>^2"
      using apply_nec_cond_one_1 by simp
  qed

lemma apply_nec_cond_one_3: shows
  "(\<k> + \<Lambda> * (\<v> - 1))* (\<k> - \<Lambda>)^(\<v> - 1) = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)"
proof -
  have "(\<k> + \<Lambda> * (\<v> - 1))* (\<k> - \<Lambda>)^(\<v> - 1) = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)"
    using apply_nec_cond_one_2 by simp
  thus ?thesis by simp
qed

lemma det_incidence: "(det N)^2 = det (N * N\<^sup>T)"
proof - 
  have "det (N * N\<^sup>T) = det N * det N\<^sup>T" 
  by (metis (full_types) N_carrier_mat det_mult local.symmetric transpose_carrier_mat)
  also have "det N * det N\<^sup>T = det N * det N"
  using N_carrier_mat det_transpose local.symmetric by auto
  then have "det (N * N\<^sup>T) = (det N)^2" by (simp add: calculation power2_eq_square)
  thus ?thesis by simp
qed 

lemma sym_det_in_mat_square:
 "(det N)^2 = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)"
proof - 
  have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
    using determinant_inc_mat_square by simp
    then have "det (N * N\<^sup>T) = (\<k> + \<Lambda> * (\<v> - 1))* (\<k> - \<Lambda>)^(\<v> - 1)"
      using rep_value_sym by simp
    also have "(\<k> + \<Lambda> * (\<v> - 1))* (\<k> - \<Lambda>)^(\<v> - 1) = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)"
      using apply_nec_cond_one_3 by simp
    then have "det (N * N\<^sup>T) = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)" 
      using calculation by argo
    then show ?thesis using det_incidence by simp
  qed

lemma power_of_k_minus_lambda_1:
  "(det N)^2 / \<k>^2 = (\<k> - \<Lambda>)^(\<v> - 1)" 
proof - 
  have "(det N)^2 = \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)" 
    using sym_det_in_mat_square by simp
  then have "(det N)^2 / \<k>^2 = (\<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)) / \<k>^2" 
    by (simp add: divide_simps)
  also have "... = \<k>^2 / \<k>^2 * (\<k> - \<Lambda>)^(\<v> - 1)" by (simp add: divide_simps)
  also have "... = 1 * (\<k> - \<Lambda>)^(\<v> - 1)" using rep_not_zero by fastforce
  also have "... = (\<k> - \<Lambda>)^(\<v> - 1)" by auto
  finally show ?thesis .
  qed

lemma power_of_k_minus_lambda_2: 
  "(det N / \<k>)^2 = (\<k> - \<Lambda>)^(\<v> - 1)"
proof -
  have "(det N)^2 / \<k>^2 = (\<k> - \<Lambda>)^(\<v> - 1)" 
    using power_of_k_minus_lambda_1 by simp
  then show ?thesis by (simp add: power_divide)
qed

lemma power_of_k_minus_lambda_3: "(sqrt(\<k> - \<Lambda>))^(\<v> - 1) \<in> \<rat>"
proof -
  have "(det N / \<k>)^2 = (\<k> - \<Lambda>)^(\<v> - 1)"
    using power_of_k_minus_lambda_2 by simp
  then have "sqrt((\<k> - \<Lambda>)^(\<v> - 1)) = sqrt((det N / \<k>)^2)" by auto
  then have "sqrt((\<k> - \<Lambda>)^(\<v> - 1)) = abs(det N / \<k>)"
    by (metis real_sqrt_abs)
  also have "(sqrt(\<k> - \<Lambda>))^(\<v> - 1) = sqrt ((\<k> - \<Lambda>)^(\<v> - 1))"
      by (simp add: real_sqrt_power) 
  then have "(sqrt(\<k> - \<Lambda>))^(\<v> - 1) = abs(det N / \<k>)"
      using calculation by presburger
  also have "abs(det N / \<k>) \<in> \<rat>" by simp
  then show ?thesis by (metis (full_types)
        \<open>sqrt (real (\<k> - \<Lambda>)) ^ (\<v> - 1) = \<bar>real_of_int (det N) / real \<k>\<bar>\<close>)
qed

lemma blocksize_gt_index: "\<k> > \<Lambda>"
  using rep_value_sym index_lt_replication by auto

lemma bruck_ryser_chowla_even_rat:
  assumes "even \<v>"
  shows "sqrt(\<k> - \<Lambda>) \<in> \<rat>"
proof -
  have diff_rat: \<open>\<k> - \<Lambda> \<in> \<rat>\<close> by simp
  have eq: "(sqrt(\<k> - \<Lambda>))^(\<v> - 1) \<in> \<rat>" using power_of_k_minus_lambda_3
    by blast
  from assms obtain m where "\<v> = 2 * m" "m > 0" using v_non_zero by auto
  then have "\<v> - 1 = 2 * m - 1" by auto
  then have "(sqrt(\<k> - \<Lambda>))^(2 * m - 1) \<in> \<rat>"
    using eq by auto
  then have rat: \<open>(sqrt(\<k> - \<Lambda>))^(2 * m) / (sqrt(\<k> - \<Lambda>)) \<in> \<rat>\<close>
    using \<open>0 < m\<close> div_by_0 div_less_iff_less_mult mult.commute
        nonzero_mult_div_cancel_left one_div_two_eq_zero pos2 power_eq_0_iff
        power_minus_mult zero_less_diff
    by (metis nat_0_less_mult_iff) 
  have eq2: \<open>(sqrt(\<k> - \<Lambda>))^(2 * m) / (sqrt(\<k> - \<Lambda>)) = 
    ((\<k> - \<Lambda>))^ m * (1/sqrt(\<k> - \<Lambda>))\<close>
    using blocksize_gt_index
    by (simp add: power_mult)
  moreover have \<open>(\<k> - \<Lambda>) ^ m \<in> \<rat>\<close>
    using diff_rat by (simp add: power_mult Rats_mult_iff)
  ultimately have \<open>1/sqrt(\<k> - \<Lambda>) \<in> \<rat>\<close>
    using rat blocksize_gt_index Rats_mult_iff by force
  then show ?thesis
    by (simp add: divide_inverse)
qed

theorem bruck_ryser_chowla_even:
  assumes "even \<v>"
  shows "sqrt(\<k> - \<Lambda>) \<in> \<nat>"
proof -
  have brc_rat: "sqrt(\<k> - \<Lambda>) \<in> \<rat>" 
    using bruck_ryser_chowla_even_rat assms by simp
  then show ?thesis using sqrt_nat_or_irrat' by blast  
qed

end

subsection \<open>v is odd\<close>

sublocale ordered_bibd \<subseteq> ordered_regular_pairwise_balance \<V>s \<B>s \<Lambda> \<r>
  by unfold_locales

context ordered_sym_bibd

begin

lemma lambda_all_ones: 
  assumes "h < \<v>" "j < \<v>"
  shows "(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) = int \<Lambda>"
proof -
  have "(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) = (int \<Lambda> \<cdot>\<^sub>m (mat \<v> \<v> (\<lambda>(j,h). 1))) $$ (j, h)"
    by (simp add: all_ones_mat_def)
  also have "... = \<Lambda>"
    using assms(1-2) by fastforce
  finally show ?thesis .
qed

lemma lambda_all_ones_extension:
  assumes "h < \<v>" "j < \<v>" "x \<in> rat mat"
  shows "(\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>} .(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
    int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2"
proof -
  have "(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) = int \<Lambda>" if "h < \<v>" "j < \<v>" for h j
    using that(1) that(2) lambda_all_ones by blast
  then have "(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0) =
                 int \<Lambda> * x $$ (j, 0) * x $$ (h, 0)" if "h < \<v>" "j < \<v>" for h j
    by (metis that(1) that(2))
  then have "(\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>} .(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
                 (\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>} .int \<Lambda> * x $$ (j, 0) * x $$ (h, 0)))"
    using sum.reindex_bij_witness by auto
  also have "... = int \<Lambda> * (\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>}. x $$ (j, 0) * x $$ (h, 0)))"
    by (simp add: algebra_simps sum_distrib_left)
  also have "... = int \<Lambda> * (\<Sum>j \<in>{0..<\<v>} .x $$ (j, 0)) * (\<Sum>h \<in>{0..<\<v>} .x $$ (h, 0))"
    by (simp add: algebra_simps sum_distrib_left)   
  also have "... = int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2"
    by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma identity_matrix_property:
  assumes "h < \<v>" "j < \<v>" "x \<in> rat mat"
  shows "int (\<r> - \<Lambda>) * (\<Sum> j \<in> {0..<\<v>}. (\<Sum> h \<in> {0..<\<v>}.  
         (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0))) = 
         int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  have delta_rule: "int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}.(\<Sum> h \<in> {0..<\<v>}. (if j = h then x $$ (h, 0) * x $$ (j, 0) else 0))) = 
        int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}.(if j \<in> {0..<\<v>} then x $$ (j, 0) * x $$ (j, 0) else 0))"
    using comm_monoid_add_class.sum.delta by auto
  have " (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0) = 
    (if j = h then x $$ (h, 0) * x $$ (j, 0) else 0)"
    if "h < \<v>" "j < \<v>" for h j by simp
  then have "int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}.(\<Sum> h \<in> {0..<\<v>}. (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0))) = 
             int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}.(\<Sum> h \<in> {0..<\<v>}. (if j = h then x $$ (h, 0) * x $$ (j, 0) else 0)))"
    if "h < \<v>" "j < \<v>" for h j using assms(1-2)
    by (simp add: that(2))
  also have "... = int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}.(if j \<in> {0..<\<v>} then x $$ (j, 0) * x $$ (j, 0) else 0))" 
    if "h < \<v>" "j < \<v>" for h j
    using delta_rule by simp
  then have "... = int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}. x $$ (j, 0) * x $$ (j, 0))"
    if "h < \<v>" "j < \<v>" for h j by force
  then have  "... = int (\<r> - \<Lambda>) *(\<Sum> j \<in> {0..<\<v>}. x $$ (j, 0)^2)"
    if "h < \<v>" "j < \<v>" for h j using power2_eq_square by metis
  then show ?thesis
    by (metis (no_types, lifting) \<open>\<And>j h. \<lbrakk>h < \<v>; j < \<v>\<rbrakk> \<Longrightarrow> int (\<r> - \<Lambda>) * (\<Sum>j = 0..<\<v>. if j \<in> {0..<\<v>} 
    then x $$ (j, 0) * x $$ (j, 0) else 0) = int (\<r> - \<Lambda>) * (\<Sum>j = 0..<\<v>. x $$ (j, 0) * x $$ (j, 0))\<close> 
    assms(2) calculation delta_rule)
qed

lemma order_times_identity_matrix:
  assumes "h < \<v>" "j < \<v>" "x \<in> rat mat"
  shows "(\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>}. (int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
        int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  have id_matrix: "(1\<^sub>m \<v>) $$ (j, h) = (if j = h then 1 else 0)"
    using one_mat_def by (simp add: assms(1) assms(2))
  hence "(int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) = int (\<r> - \<Lambda>) * (if j = h then 1 else 0)"
    using assms(1-2) by fastforce

  then have "(\<Sum> j \<in> {0..<\<v>}. (\<Sum> h \<in> {0..<\<v>}. (int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
             (\<Sum> j \<in> {0..<\<v>}. (\<Sum> h \<in> {0..<\<v>}. int (\<r> - \<Lambda>) * (if j = h then 1 else 0) * x $$ (j, 0) * x $$ (h, 0)))"
    by simp
  also have "... = int (\<r> - \<Lambda>) * (\<Sum> j \<in> {0..<\<v>}. (\<Sum> h \<in> {0..<\<v>}.  
         (if j = h then 1 else 0) * x $$ (h, 0) * x $$ (j, 0)))" 
         by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using identity_matrix_property assms(2) assms(3) by blast
  finally show ?thesis .
qed

lemma combine_r_lambda_terms:
  assumes "h < \<v>" "j < \<v>" "x \<in> rat mat"
  shows "(\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}.(int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0))) = int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 + 
    int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  have lam: "(\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>} .(int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
    int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2" 
    using lambda_all_ones_extension by fastforce
  have ord: "(\<Sum>j \<in>{0..<\<v>} .(\<Sum>h \<in>{0..<\<v>}.(int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) =
        int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)" 
    using order_times_identity_matrix by force
  then show ?thesis using lam ord by argo
qed

lemma brc_x_identity:
  assumes "x \<in> rat mat" "h < \<v>" "j < \<v>"
  shows "(\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. (\<Sum>i \<in> {0..<\<v>}.  
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0))) =
     int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
     int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  have matdef: "(\<Sum>i \<in>{0..<\<v>} . 
    of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = (N * N\<^sup>T) $$ (j, h)" 
    if "h < \<v>" "j < \<v>" for h j
    using transpose_mat_mult_entries[of "j" "N" "h"]
    local.symmetric that by fastforce
  have matcond: "(N * N\<^sup>T) $$ (j, h) = 
    (int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h)"
    if "h < \<v>" "j < \<v>" for h j 
    using rpbd_incidence_matrix_cond that(1) that(2) by fastforce
  have sum_eq_rLambda: "(\<Sum>i \<in> {0..<\<v>}. of_int (N $$ (j,i)) * of_int (N $$ (h,i))) = 
    (int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h)"
    if "h < \<v>" "j < \<v>" for h j
    using matdef[OF that] matcond[OF that] by argo
  have "(\<Sum>i \<in> {0..<\<v>}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0) = 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h)) * 
    x $$ (j, 0) * x $$ (h, 0)" if "h < \<v>" "j < \<v>" for h j
    using sum_eq_rLambda[OF that]
    by (metis (mono_tags, lifting))
  then have "(\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. (\<Sum>i \<in> {0..<\<v>}. 
    of_int (N $$ (j, i)) * of_int (N $$ (h, i))) * x $$ (j, 0) * x $$ (h, 0))) = 
    (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h)) *
     x $$ (j, 0) * x $$ (h, 0)))" by (intro sum.mono_neutral_cong_right) auto
  also have "... = (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)) +
    (int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0))) +
    (\<Sum>h \<in> {0..<\<v>}.(int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" by (simp add: sum.distrib)
  also have "... = (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. 
    ((int \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>)) $$ (j, h) * x $$ (j, 0) * x $$ (h, 0)))) +
    (\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. (int (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)) $$ (j, h) * 
    x $$ (j, 0) * x $$ (h, 0)))" 
    by (simp add: sum.distrib)
  also have final_equ:  "... = int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 + 
     int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using combine_r_lambda_terms assms(1-3) by simp
  finally show ?thesis .
qed

lemma brc_x_equation:
  assumes "x \<in> rat mat" "h < \<v>" "j < \<v>"
  shows "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
     int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
     int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  have r_eq_k: "\<r> = \<k>" using rep_value_sym by simp
  have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
    (\<Sum>i \<in> {0..<\<v>}. (\<Sum>j \<in> {0..<\<v>}. of_int (N $$ (j, i)) *
    x $$ (j, 0)) * (\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h, 0)))"
    by (simp add: power2_eq_square)
  also have "... = (\<Sum>i \<in> {0..<\<v>}. (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}.
    (of_int (N $$ (j, i)) * x $$ (j,0)) * (of_int (N $$ (h,i)) * x $$ (h,0)))))"
    by (metis (no_types) sum_product)
  also have "... = (\<Sum>i \<in> {0..<\<v>}. (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}.
    of_int (N $$ (j, i)) * (x $$ (j,0) * of_int (N $$ (h,i))) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i \<in> {0..<\<v>}. (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}.
    of_int (N $$ (j, i)) * (of_int (N $$ (h,i)) * x $$ (j,0)) * x $$ (h,0))))"
    by (metis (no_types, lifting) mult_of_int_commute sum.cong)
  also have "... = (\<Sum>i \<in> {0..<\<v>}. (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}.
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. (\<Sum>i \<in> {0..<\<v>}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * x $$ (j,0) * x $$ (h,0))))"
    using sum_reorder_triple[of "\<lambda> i j h . of_int (N $$ (j, i)) * of_int (N $$ (h,i)) * 
        x $$ (j,0) * x $$ (h,0)" "{0..<\<v>}" "{0..<\<v>}" "{0..<\<v>}"] 
    by blast
  also have "... = (\<Sum>j \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. (\<Sum>i \<in> {0..<\<v>}.  
    of_int (N $$ (j, i)) * of_int (N $$ (h,i))) * x $$ (j,0) * x $$ (h,0)))"
    by (simp add: algebra_simps sum_distrib_left sum_distrib_right)
  also have "... = int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
     int (\<r> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using brc_x_identity assms(1-3) by simp
  also have "... = int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0)))^2 +
     int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using r_eq_k by simp
  finally show ?thesis .
qed


lemma brc_x_equation_new:
  fixes x :: "rat mat"
  shows "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))^2) =
     of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
     of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
proof -
  
  (* We can pick arbitrary h < \<v> and j < \<v> since they're not used in the conclusion *)
  obtain h j where hj: "h < \<v>" "j < \<v>"
    using positive_v by (metis gr0I not_less0)
    
  (* Now apply the lemma from the attached document *)
  have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
        int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
        int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using brc_x_equation[OF `x \<in> rat mat` hj] .
    
  (* Now we need to show our version is the same *)
  have eq1: "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))^2) =
            (\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h,0))^2)"
  proof -
    have "\<And>i h. i < \<v> \<Longrightarrow> h < \<v> \<Longrightarrow> N $$ (h,i) * x $$ (h,0) = of_int (N $$ (h,i)) * x $$ (h,0)"
      by simp  (* N is an integer matrix, so N $$ (h,i) is already an integer *)
    thus ?thesis by auto
  qed
  
  have eq2: "int \<Lambda> = of_int \<Lambda>" by simp
  have eq3: "int (\<k> - \<Lambda>) = of_int (\<k> - \<Lambda>)" by simp
  
  from `(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int (N $$ (h,i)) * x $$ (h,0))^2) =
        int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
        int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)`
  have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))^2) =
        of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
    using eq1 eq2 eq3 by simp
    
  thus ?thesis .
qed

fun rightside :: "((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat)) \<Rightarrow> 
                  (rat \<times> rat \<times> rat \<times> rat)" where
  "rightside((a, b, c, d),(x0, x1, x2, x3)) = (x0, x1, x2, x3)"

fun y_reversible :: "((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat)) \<Rightarrow> 
             ((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat))" where
  "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = ((a, b, c, d),
   ( (of_nat a * x0 + of_nat b * x1 + of_nat c * x2 + of_nat d * x3),
   (- of_nat b * x0 + of_nat a * x1 - of_nat d * x2 + of_nat c * x3),
   (- of_nat c * x0 + of_nat d * x1 + of_nat a * x2 - of_nat b * x3),
   (- of_nat d * x0 - of_nat c * x1 + of_nat b * x2 + of_nat a * x3)))"

fun y_of :: "((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat)) \<Rightarrow> 
                  (rat \<times> rat \<times> rat \<times> rat)" where
  "y_of((a, b, c, d),(x0, x1, x2, x3)) = rightside(y_reversible((a, b, c, d),(x0, x1, x2, x3)))"

fun y_inv_reversible ::"((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat)) \<Rightarrow> 
             ((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat))" where
  "y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)) = ((a, b, c, d),
  ((of_nat a)*y0 - (of_nat b)*y1 - (of_nat c)*y2 - (of_nat d)*y3)/of_nat(a^2 + b^2 + c^2 + d^2), 
  ((of_nat b)*y0 + (of_nat a)*y1 + (of_nat d)*y2 - (of_nat c)*y3)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat c)*y0 + (of_nat a)*y2 + (of_nat b)*y3 - (of_nat d)*y1)/of_nat(a^2 + b^2 + c^2 + d^2),
  ((of_nat d)*y0 + (of_nat c)*y1 + (of_nat a)*y3 - (of_nat b)*y2)/of_nat(a^2 + b^2 + c^2 + d^2))"

fun y_inv_of :: "((nat \<times> nat \<times> nat \<times> nat) \<times> (rat \<times> rat \<times> rat \<times> rat)) \<Rightarrow> 
                  (rat \<times> rat \<times> rat \<times> rat)" where
  "y_inv_of((a, b, c, d),(y0, y1, y2, y3)) = 
   rightside(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"

fun one_of :: "(rat \<times> rat \<times> rat \<times> rat) \<Rightarrow> rat" where
  "one_of(y0, y1, y2, y3) = y0"

fun two_of :: "(rat \<times> rat \<times> rat \<times> rat) \<Rightarrow> rat" where
  "two_of(y0, y1, y2, y3) = y1"

fun three_of :: "(rat \<times> rat \<times> rat \<times> rat) \<Rightarrow> rat" where
  "three_of(y0, y1, y2, y3) = y2"

fun four_of :: "(rat \<times> rat \<times> rat \<times> rat) \<Rightarrow> rat" where
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
  assumes "a^2 + b^2 + c^2 + d^2 \<noteq> 0"
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
  assumes "a^2 + b^2 + c^2 + d^2 \<noteq> 0"
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
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
           "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"       
  shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
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
    one_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
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
    two_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
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
    three_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
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
    four_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
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
  have sumdef: "(\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x $$ (m-4,0) + of_int(N $$ (m-3,m-i-1)) * x $$ (m-3,0) + 
        of_int(N $$ (m-2,m-i-1)) * x $$ (m-2,0) + of_int(N $$ (m-1,m-i-1)) * x $$ (m-1,0)" 
    by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
  have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =
        (\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) + 
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> h . 
    (of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-i-1)) * x0 + of_int(N $$ (m-3,m-i-1)) * x1 +
        of_int(N $$ (m-2,m-i-1)) * x2 + of_int(N $$ (m-1,m-i-1)) * x3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    using sumdef assms(4-8) by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" using sum by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-i-1)) * (of_nat a)*?y0/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)*?y0/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat c)*?y0/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)*?y0/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat b)*?y1/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)*?y1/?D -
    of_int(N $$ (m-2,m-i-1)) * (of_nat d)*?y1/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)*?y1/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat c)*?y2/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)*?y2/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat a)*?y2/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)*?y2/?D -
    of_int(N $$ (m-4,m-i-1)) * (of_nat d)*?y3/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-i-1)) * (of_nat b)*?y3/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    (of_int(N $$ (m-4,m-i-1)) * (of_nat a)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat b)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat d)/?D) * ?y0 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat a)/?D -
     of_int(N $$ (m-2,m-i-1)) * (of_nat d)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat c)/?D) * ?y1 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat c)/?D + of_int(N $$ (m-3,m-i-1)) * (of_nat d)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat a)/?D - of_int(N $$ (m-1,m-i-1)) * (of_nat b)/?D) * ?y2 +
    (-of_int(N $$ (m-4,m-i-1)) * (of_nat d)/?D - of_int(N $$ (m-3,m-i-1)) * (of_nat c)/?D +
     of_int(N $$ (m-2,m-i-1)) * (of_nat b)/?D + of_int(N $$ (m-1,m-i-1)) * (of_nat a)/?D) * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    ?e00 * ?y0 + ?e01 * ?y1 + ?e02 * ?y2 + ?e03 * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))" by blast
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
  assumes "a^2 + b^2 + c^2 + d^2 = (\<k> - \<Lambda>)"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"   
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
proof -
  
  have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
     using linear_comb_of_y_part_1 assms(1-12) by simp
  then have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
    by simp

   then obtain e0 e1 e2 e3 where eq1:
    "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0)) = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-i-1)) * x $$ (m-h-1,0))"
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

lemma linear_comb_of_y_part_1_i3:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes x :: "rat mat"
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
           "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"    
        shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
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
  let ?e0 = "of_int(N $$ (m-4,m-4)) * (of_nat a)/?D + of_int(N $$ (m-3,m-4)) * (of_nat b)/?D +
             of_int(N $$ (m-2,m-4)) * (of_nat c)/?D + of_int(N $$ (m-1,m-4)) * (of_nat d)/?D"
  let ?e1 = "-of_int(N $$ (m-4,m-4)) * (of_nat b)/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)/?D -
              of_int(N $$ (m-2,m-4)) * (of_nat d)/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)/?D"
  let ?e2 = "-of_int(N $$ (m-4,m-4)) * (of_nat c)/?D + of_int(N $$ (m-3,m-4)) * (of_nat d)/?D +
              of_int(N $$ (m-2,m-4)) * (of_nat a)/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)/?D"
  let ?e3 = "-of_int(N $$ (m-4,m-4)) * (of_nat d)/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)/?D +
              of_int(N $$ (m-2,m-4)) * (of_nat b)/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)/?D"

  have oneof: "x0 = 
    one_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x0 = ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D"
    by simp
  then have first_1: "of_int(N $$ (m-4,m-4)) * x0 = of_int(N $$ (m-4,m-4)) *
    ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - (of_nat d)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have first_2: "of_int(N $$ (m-4,m-4)) * ((of_nat a)*?y0 - (of_nat b)*?y1 - (of_nat c)*?y2 - 
    (of_nat d)*?y3)/?D = of_int(N $$ (m-4,m-4)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-4)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-4)) * (of_nat c)*?y2/?D -
    of_int(N $$ (m-4,m-4)) * (of_nat d)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  then have first: "of_int(N $$ (m-4,m-4)) * x0 = of_int(N $$ (m-4,m-4)) * (of_nat a)*?y0/?D - 
    of_int(N $$ (m-4,m-4)) * (of_nat b)*?y1/?D - of_int(N $$ (m-4,m-4)) * (of_nat c)*?y2/?D - 
    of_int(N $$ (m-4,m-4)) * (of_nat d)*?y3/?D" 
    using first_1 first_2 by argo

  have twoof: "x1 = 
    two_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x1 = ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D"
    by simp
  then have second_1: "of_int(N $$ (m-3,m-4)) * x1 = of_int(N $$ (m-3,m-4)) *
    ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - (of_nat c)*?y3)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right)
  have second_2: "of_int(N $$ (m-3,m-4)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + (of_nat d)*?y2 - 
    (of_nat c)*?y3)/?D = of_int(N $$ (m-3,m-4)) * ((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have second_3: "of_int(N $$ (m-3,m-4)) *((of_nat b)*?y0 + (of_nat a)*?y1 + 
    (of_nat d)*?y2)/?D = (of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0 + 
    of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1 + of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have second_4: "(of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2)/?D = of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D + 
    of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0 + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1 + 
    of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2)/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D = 
    of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D + 
    of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D" 
    by presburger
  then have second: "of_int(N $$ (m-3,m-4)) * x1 = of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D +
     of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D + of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D - 
     of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D"
    using second_1 second_2 second_3 second_4 by argo

  have threeof: "x2 = 
    three_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x2 = ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D"
    by simp
  then have third_1: "of_int(N $$ (m-2,m-4)) * x2 = of_int(N $$ (m-2,m-4)) *
    ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - (of_nat d)*?y1)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have third_2: "of_int(N $$ (m-2,m-4)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3 - 
    (of_nat d)*?y1)/?D = of_int(N $$ (m-2,m-4)) * ((of_nat c)*?y0 + (of_nat a)*?y2 + (of_nat b)*?y3)/?D - 
    of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have third_3: "of_int(N $$ (m-2,m-4)) *((of_nat c)*?y0 + (of_nat a)*?y2 + 
    (of_nat b)*?y3)/?D = (of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0 + 
    of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2 + of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have third_4: "(of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3)/?D = of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D + 
    of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0 + of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2 + 
    of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3)/?D - of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D = 
    of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D + of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D + 
    of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D - of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D" 
    by presburger
  then have third: "of_int(N $$ (m-2,m-4)) * x2 = of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D +
     of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D - 
     of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D"
    using third_1 third_2 third_3 third_4 by argo

  have fourof: "x3 = 
    four_of(rightside(y_inv_reversible(y_reversible((a, b, c, d),(x0, x1, x2, x3)))))"
    using key by auto
  then have "x3 = ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D"
    by simp
  then have fourth_1: "of_int(N $$ (m-1,m-4)) * x3 = of_int(N $$ (m-1,m-4)) *
    ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - (of_nat b)*?y2)/?D" 
    by (metis (mono_tags, lifting) times_divide_eq_right) 
  have fourth_2: "of_int(N $$ (m-1,m-4)) * ((of_nat d)*?y0 + (of_nat c)*?y1 + (of_nat a)*?y3 - 
    (of_nat b)*?y2)/?D = of_int(N $$ (m-1,m-4)) * ((of_nat d)*?y0 + (of_nat c)*?y1 +
    (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D" 
    by (simp add: of_rat_diff of_rat_mult right_diff_distrib divide_simps)
  have fourth_3: "of_int(N $$ (m-1,m-4)) *((of_nat d)*?y0 + (of_nat c)*?y1 + 
    (of_nat a)*?y3)/?D = (of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0 + 
    of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1 + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3)/?D"
    by (simp add: of_rat_add of_rat_mult distrib_left)
  have fourth_4: "(of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3)/?D = of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D + 
    of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D"
    by (simp add: of_rat_add of_rat_mult add_divide_distrib)
  then have "(of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0 + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1 + 
    of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3)/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D = 
    of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D + 
    of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D" 
    by presburger
  then have fourth: "of_int(N $$ (m-1,m-4)) * x3 = of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D +
     of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D - 
     of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D"
    using fourth_1 fourth_2 fourth_3 fourth_4 by argo 

  have sum: "of_int(N $$ (m-4,m-4)) * x0 + of_int(N $$ (m-3,m-4)) * x1 + 
    of_int(N $$ (m-2,m-4)) * x2 + of_int(N $$ (m-1,m-4)) * x3 =
    of_int(N $$ (m-4,m-4)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-4)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-4)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-4)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D"
    using first second third fourth by linarith
  have sumdef: "(\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-4)) * x $$ (m-4,0) + of_int(N $$ (m-3,m-4)) * x $$ (m-3,0) + 
        of_int(N $$ (m-2,m-4)) * x $$ (m-2,0) + of_int(N $$ (m-1,m-4)) * x $$ (m-1,0)" 
    by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
  have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
        (\<Sum>h \<in> {0..<4}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) + 
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> h . 
    (of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
        of_int(N $$ (m-4,m-4)) * x0 + of_int(N $$ (m-3,m-4)) * x1 +
        of_int(N $$ (m-2,m-4)) * x2 + of_int(N $$ (m-1,m-4)) * x3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    using sumdef assms(4-8) by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-4)) * (of_nat a)*?y0/?D - of_int(N $$ (m-4,m-4)) * (of_nat b)*?y1/?D - 
    of_int(N $$ (m-4,m-4)) * (of_nat c)*?y2/?D - of_int(N $$ (m-4,m-4)) * (of_nat d)*?y3/?D +
    of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D +
    of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D - of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D + 
    of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D + of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D + 
    of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D - 
    of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))" using sum by argo
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =   
    of_int(N $$ (m-4,m-4)) * (of_nat a)*?y0/?D + of_int(N $$ (m-3,m-4)) * (of_nat b)*?y0/?D +
    of_int(N $$ (m-2,m-4)) * (of_nat c)*?y0/?D + of_int(N $$ (m-1,m-4)) * (of_nat d)*?y0/?D -
    of_int(N $$ (m-4,m-4)) * (of_nat b)*?y1/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)*?y1/?D -
    of_int(N $$ (m-2,m-4)) * (of_nat d)*?y1/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)*?y1/?D -
    of_int(N $$ (m-4,m-4)) * (of_nat c)*?y2/?D + of_int(N $$ (m-3,m-4)) * (of_nat d)*?y2/?D +
    of_int(N $$ (m-2,m-4)) * (of_nat a)*?y2/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)*?y2/?D -
    of_int(N $$ (m-4,m-4)) * (of_nat d)*?y3/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)*?y3/?D +
    of_int(N $$ (m-2,m-4)) * (of_nat b)*?y3/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)*?y3/?D +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
    (of_int(N $$ (m-4,m-4)) * (of_nat a)/?D + of_int(N $$ (m-3,m-4)) * (of_nat b)/?D +
     of_int(N $$ (m-2,m-4)) * (of_nat c)/?D + of_int(N $$ (m-1,m-4)) * (of_nat d)/?D) * ?y0 +
    (-of_int(N $$ (m-4,m-4)) * (of_nat b)/?D + of_int(N $$ (m-3,m-4)) * (of_nat a)/?D -
     of_int(N $$ (m-2,m-4)) * (of_nat d)/?D + of_int(N $$ (m-1,m-4)) * (of_nat c)/?D) * ?y1 +
    (-of_int(N $$ (m-4,m-4)) * (of_nat c)/?D + of_int(N $$ (m-3,m-4)) * (of_nat d)/?D +
     of_int(N $$ (m-2,m-4)) * (of_nat a)/?D - of_int(N $$ (m-1,m-4)) * (of_nat b)/?D) * ?y2 +
    (-of_int(N $$ (m-4,m-4)) * (of_nat d)/?D - of_int(N $$ (m-3,m-4)) * (of_nat c)/?D +
     of_int(N $$ (m-2,m-4)) * (of_nat b)/?D + of_int(N $$ (m-1,m-4)) * (of_nat a)/?D) * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))" by (simp add: algebra_simps)
  then have "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
    ?e00 * ?y0 + ?e01 * ?y1 + ?e02 * ?y2 + ?e03 * ?y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))" by blast
  then show ?thesis by blast
qed

lemma linear_comb_of_y_part_2_i3:
  fixes a :: "nat"
  fixes b :: "nat"
  fixes c :: "nat"
  fixes d :: "nat"
  fixes y0 :: "rat"
  fixes y1 :: "rat"
  fixes y2 :: "rat"
  fixes y3 :: "rat"
  fixes x :: "rat mat"
  assumes "a^2 + b^2 + c^2 + d^2 = (\<k> - \<Lambda>)"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"   
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
    e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
proof -
  
  have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
     using linear_comb_of_y_part_1_i3 assms(1-8) by simp
  then have "\<exists>e0 e1 e2 e3 :: rat.(\<Sum>h \<in> {0..<m}. 
          of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =   
          e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
    by simp

   then obtain e0 e1 e2 e3 where eq1:
    "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
    e0 * one_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e1 * two_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e2 * three_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    e3 * four_of(y_of((a, b, c, d),(x0, x1, x2, x3))) +
    (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
     by fast

  have "((a, b, c, d),(x0, x1, x2, x3)) = 
        y_inv_reversible((a, b, c, d),(y0, y1, y2, y3))"
    using assms(9-12) by simp
  then have "y_reversible((a, b, c, d),(x0, x1, x2, x3)) = 
        y_reversible(y_inv_reversible((a, b, c, d),(y0, y1, y2, y3)))"
    by simp
  then have eq2: "y_reversible((a, b, c, d),(x0, x1, x2, x3)) =
    ((a, b, c, d),(y0, y1, y2, y3))" 
    using y_inverses_part_2 assms(1-12) blocksize_gt_index 
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
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
  shows "of_int(\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
         of_int(\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
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
          of_nat (\<k> - \<Lambda>) * (x0^2 + x1^2 + x2^2 + x3^2)" using assms(1)
    by presburger
  then have keyform: "one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
          two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
          four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 = 
          of_int(\<k> - \<Lambda>) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 +
          (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)" using eq by simp
  have sumdef: "(\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) = (x $$ (m-1,0))^2 + 
        (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2" by (simp add: numeral.simps(2,3))
  have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(3) by auto
  have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
  have "(\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        (\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) + 
        (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
    using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> j . (x $$ (m-j-1, 0))^2"] 
    by (metis (no_types, lifting) finite_atLeastLessThan)
  then have "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (m-j-1, 0))^2) + 
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)" using algebra_simps by simp
  then have "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) =
        of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
        of_int (\<k> - \<Lambda>) * ((x $$ (m-1,0))^2 + (x $$ (m-2,0))^2 + (x $$ (m-3,0))^2 + (x $$ (m-4,0))^2)"
    using sumdef algebra_simps by auto
  then have "of_nat(\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_nat(\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
            (one_of(y_of((a, b, c, d),(x0, x1, x2, x3)))^2 +
             two_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             three_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2 +
             four_of(y_of((a, b, c, d), (x0, x1, x2, x3)))^2)"
    using keyform algebra_simps by auto
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
  assumes "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
          "\<v> \<ge> m" "m > 3" "i \<in> {0..<4}" "x0 = x $$ (m-4,0)" 
          "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
          "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
          "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  shows   "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
           of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
           y0^2 + y1^2 + y2^2 + y3^2"
proof -
  have eq1: "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<m}. (x $$ (m-j-1, 0))^2) = 
             of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2) +
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
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"        
        "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
         e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
         (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
        "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
        (e10 * y1 + e20 * y2 + e30 * y3 +
        (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  shows "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
proof -
  have "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
               (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
   proof (cases "e00 = 1")
     case True   
    then have "y0 = -(e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y0 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using eq by simp
    then have "(-y0)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y0 = (e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))) / (1 - e00)"
      using assms(5) by auto
    then have "(1 - e00) * y0 = e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y0 = e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y0 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y0^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))^2"
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
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
            e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
           "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
           (e01 * y0 + e21 * y2 + e31 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  shows "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
proof -
  have "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
   proof (cases "e11 = 1")
     case True   
    then have "y1 = -(e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y1 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using eq by simp
    then have "(-y1)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by auto
   next
    case False
    then have "y1 = (e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))) / (1 - e11)"
      using assms(5) by auto
    then have "(1 - e11) * y1 = e01 * y0 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y1 = e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y1 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y1^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))^2"
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
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
           e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
          "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
           (e02 * y0 + e12 * y1 + e32 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))" 
  shows "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
proof -
  have "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
               (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
   proof (cases "e22 = 1")
     case True   
    then have "y2 = -(e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y2 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using eq by simp
    then have "(-y2)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y2 = (e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))) / (1 - e22)"
      using assms(5) by auto
    then have "(1 - e22) * y2 = e02 * y0 + e12 * y1 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y2 = e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y2 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y2^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))^2"
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
  assumes "of_nat(a^2 + b^2 + c^2 + d^2) = of_int(\<k> - \<Lambda>)" "\<v> \<ge> m" "m > 3"
          "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
           e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
          "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
           (e03 * y0 + e13 * y1 + e23 * y2 +
           (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"
  shows "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
           (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
proof -
  have first_fact: "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
   proof (cases "e33 = 1")
     case True   
    then have "y3 = -(e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2"
      using assms(5) by auto
    then have eq: "-y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using True by (simp add: algebra_simps)
    have "e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using assms(4) by simp
    then have "-y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using eq by simp
    then have "(-y3)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y3 = (e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))) / (1 - e33)"
      using assms(5) by auto
    then have "(1 - e33) * y3 = e03 * y0 + e13 * y1 + e23 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y3 = e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using assms(4) by simp     
    then have "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis by simp
qed

lemma brc_v_1_mod_4:
      assumes "\<v> mod 4 = 1"
        shows "\<exists>x :: rat mat.(\<Sum>j \<in> {4..<5}.
               ((\<Sum>h \<in> {0..<5}. of_int(N $$ (4-h,4-j)) * x $$ (4-h,0)) +
               (\<Sum>h \<in> {5..<\<v>}. of_int(N $$ (h,4-j)) * x $$ (h,0)))^2) =
                of_nat \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_nat (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<5}. (x $$ (4-j, 0))^2)"
proof -
  obtain a b c d where lag_eq:
    "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
    using blocksize_gt_index sum_of_four_squares by metis

  fix h :: "nat"
  fix i :: "nat"
  fix j :: "nat"
  obtain m where ineq: "\<v> \<ge> m" "m > 3"
    using assms t_design_min_v by force
  define n where "n = (\<v>-m) div 4"
  fix y0 :: "rat"
  fix y1 :: "rat"
  fix y2 :: "rat"
  fix y3 :: "rat"
  define x0 where "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x1 where "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x2 where "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x3 where "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
  define x :: "rat mat" where  "x = mat m 1 (\<lambda>(i, j).
     if j = 0 then
       if i = m - 4 then x0
       else if i = m - 3 then x1
       else if i = m - 2 then x2
       else if i = m - 1 then x3
       else 0
     else 0)"

    have "\<exists>e00 e10 e20 e30 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) =
          e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2_i3 lag_eq ineq by auto
    then obtain e00 e10 e20 e30 where eq3:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) = 
          e00 * y0 + e10 * y1 + e20 * y2 + e30 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e01 e11 e21 e31 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
                 e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=2] ineq lag_eq by auto
    then obtain e01 e11 e21 e31 where eq2:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) = 
          e01 * y0 + e11 * y1 + e21 * y2 + e31 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e02 e12 e22 e32 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
                 e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=1] ineq lag_eq by auto
    then obtain e02 e12 e22 e32 where eq1:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) = 
          e02 * y0 + e12 * y1 + e22 * y2 + e32 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0))"
      by fast
    have "\<exists>e03 e13 e23 e33 :: rat.(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
                 e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using linear_comb_of_y_part_2[where i=0] ineq lag_eq by auto
    then obtain e03 e13 e23 e33 where eq0:
         "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
          e03 * y0 + e13 * y1 + e23 * y2 + e33 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
     by fast

  define y0 where "y0 = (if e00 = 1 then -(e10 * y1 + e20 * y2 + e30 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/2 else  
                  (e10 * y1 + e20 * y2 + e30 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0)))/(1-e00))"
  define y1 where "y1 = (if e11 = 1 then -(e01 * y0 + e21 * y2 + e31 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/2 else  
                  (e01 * y0 + e21 * y2 + e31 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0)))/(1-e11))"
  define y2 where "y2 = (if e22 = 1 then -(e02 * y0 + e12 * y1 + e32 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/2 else  
                  (e02 * y0 + e12 * y1 + e32 * y3 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0)))/(1-e22))"
  define y3 where "y3 = (if e33 = 1 then -(e03 * y0 + e13 * y1 + e23 * y2 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
                  (e03 * y0 + e13 * y1 + e23 * y2 +
                  (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e33))"

  let ?L0 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
  let ?L1 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
  let ?L2 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
  let ?L3 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
   
   have sumdef: "(\<Sum>j \<in> {0..<4}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) = 
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2"
     by (simp add: numeral.simps(2,3))
   have split1: "{0..<m} = {0..<4} \<union> {4..<m}" using ineq by auto
   have inter1: "{} = {0..<4} \<inter> {4..<m}" by auto
   have trick1: "(\<Sum>j \<in> {0..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
        (\<Sum>j \<in> {0..<4}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) + 
        (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
     using split1 inter1 sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> j . 
      ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
      (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2"] 
     by (metis (no_types, lifting) finite_atLeastLessThan)
   then have lhs: "(\<Sum>j \<in> {0..<m}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2 + 
                  (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
    using sumdef by algebra

    have "(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0)) = 
        (\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>h. \<v>-h-1" "\<lambda>h. \<v>-h-1"]) auto
    then have first: "(\<Sum>i \<in> {0..<\<v>}. (\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))) = 
        (\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)))"
      by simp
    have "(\<Sum>i \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)) =
        (\<Sum>i \<in> {0..<\<v>}. N $$ (\<v>-h-1,\<v>-i-1) * x $$ (\<v>-h-1,0))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>i. \<v>-i-1" "\<lambda>i. \<v>-i-1"]) auto
    have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))) = 
        (\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (\<v>-h-1,i) * x $$ (\<v>-h-1,0)))"
      using first by auto

    have "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,i) * x $$ (h,0))^2) =
                of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using brc_x_equation by auto
    then have base: "(\<Sum>i \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. N $$ (h,\<v>-i+1) * x $$ (h,0))^2) =
                of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      by auto
    have split2: "{0..<\<v>} = {0..<4} \<union> {4..<\<v>}" using ineq by auto
    have inter2: "{} = {0..<4} \<inter> {4..<\<v>}" by auto
    have trick2: "(\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
          (\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
          (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2)"
      using split2 inter2 sum.union_disjoint[of "{0..<4}" "{4..<\<v>}" "\<lambda> j . 
      ((\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0)))^2"]
      by (metis (no_types, lifting) finite_atLeastLessThan)
    have "(\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2) =
          (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
          (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      using split2 inter2 sum.union_disjoint[of "{0..<4}" "{4..<\<v>}" "\<lambda> j. (x $$ (j, 0))^2"]
      by auto
    then have trick3: "of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2) =
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      by (simp add: algebra_simps)
    have "(\<Sum>j \<in> {0..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
      of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
      of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using base by simp

    then have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
      (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
       of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<\<v>}. (x $$ (j, 0))^2)"
      using trick2 by simp

    then have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) +
      (\<Sum>j \<in> {4..<\<v>}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))^2) =
       of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {0..<4}. (x $$ (j, 0))^2) +
       of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<\<v>}. (x $$ (j, 0))^2)"
      using trick3 by simp

  have "(\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. 
        of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
         of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
         of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
  proof (induction n)
    case 0
    have "(\<Sum>j \<in> {0..<4}.(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (\<v>-h-1,\<v>-j-1)) * x $$ (\<v>-h-1,0))) = 
          ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2"
      using sumdef by simp





    then show ?case 
      using base by auto
  next
    case (Suc n) 
    have split2: "{0..<\<v>} = {0..<m} \<union> {m..<\<v>}" using ineq by auto
    have inter2: "{} = {0..<m} \<inter> {m..<\<v>}" by auto
    have split_sum: "(\<Sum>h \<in> {0..<\<v>}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0)) =
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0)) +
          (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0))"
     using split2 inter2 sum.union_disjoint[of "{0..<m}" "{m..<\<v>}" "\<lambda> h . 
      (of_int(N $$ (h,\<v>-j-1)) * x $$ (h,0))"] 
     by (metis (no_types, lifting) finite_atLeastLessThan)
 

 

   then show ?thesis by simp
 qed
  oops
qed


lemma induction_step_3b:
      assumes   "a \<in> \<nat>" "b \<in> \<nat>" "c \<in> \<nat>" "d \<in> \<nat>" 
                "x0 \<in> \<rat>" "x1 \<in> \<rat>" "x2 \<in> \<rat>" "x3 \<in> \<rat>"
                "a^2 + b^2 + c^2 + d^2 = \<k> - \<Lambda>"
                "x \<in> rat mat" "\<v> \<ge> m" "m > 3" "x0 = x $$ (m-4,0)" 
                "x1 = x $$ (m-3,0)" "x2 = x $$ (m-2,0)" "x3 = x $$ (m-1,0)"
                "x0 = one_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
                "x1 = two_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
                "x2 = three_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
                "x3 = four_of(y_inv_of((a, b, c, d),(y0, y1, y2, y3)))"
                "y0 \<in> \<rat>" "y1 \<in> \<rat>" "y2 \<in> \<rat>" "y3 \<in> \<rat>"
                "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) = 
                 e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
                "y3 = (if e3 = 1 then -(e0 * y0 + e1 * y1 + e2 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2 else  
                 (e0 * y0 + e1 * y1 + e2 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/(1-e3))"
                "((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2 + 
                 (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  y3^2 + of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)" 
          shows "(\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
                  of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
proof -
  let ?L0 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-4)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-4)) * x $$ (h,0))"
  let ?L1 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-3)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-3)) * x $$ (h,0))"
  let ?L2 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-2)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-2)) * x $$ (h,0))"
  let ?L3 = "(\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"

   have sumdef: "(\<Sum>j \<in> {0..<4}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) = 
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2"
                  by (simp add: numeral.simps(2,3))
   have split: "{0..<m} = {0..<4} \<union> {4..<m}" using assms(12) by auto
   have inter: "{} = {0..<4} \<inter> {4..<m}" by auto
   have "(\<Sum>j \<in> {0..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
        (\<Sum>j \<in> {0..<4}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) + 
        (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
     using split inter sum.union_disjoint[of "{0..<4}" "{4..<m}" "\<lambda> j . 
      ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
      (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2"] 
     by (metis (no_types, lifting) finite_atLeastLessThan)

  then have lhs: "(\<Sum>j \<in> {0..<m}.((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
                  ?L0^2 + ?L1^2 + ?L2^2 + ?L3^2 + 
                  (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
                  (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2)"
    using sumdef by algebra

  have first_fact: "y3^2 = ?L3^2"
   proof (cases "e3 = 1")
     case True   
    then have "y3 = -(e0 * y0 + e1 * y1 + e2 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))/2"
      using assms(26) by auto
    then have eq: "-y3 = e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using True by auto
    have "e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
          (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))  = 
          (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0))"
      using assms(25) by simp
    then have "-y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using eq by simp
    then have "(-y3)^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by argo
    then show ?thesis
      by simp
   next
    case False
    then have "y3 = (e0 * y0 + e1 * y1 + e2 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))) / (1 - e3)"
      using assms(26) by auto
    then have "(1 - e3) * y3 = e0 * y0 + e1 * y1 + e2 * y2 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using False by auto
    then have eq2: "y3 = e0 * y0 + e1 * y1 + e2 * y2 + e3 * y3 +
                 (\<Sum>h \<in> {4..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
                 (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      by (simp add: algebra_simps)
    then have "y3 = (\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0))"
      using assms(25) by simp     
    then have "y3^2 = ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
              (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2"
      by simp
    then show ?thesis
      by (simp add: algebra_simps)
  qed

  have "((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-1)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-1)) * x $$ (h,0)))^2 + 
        (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
        (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
         y3^2 + of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
         of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"   
    using assms(27) by simp
  then have "?L3^2 + 
             (\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
             y3^2 + of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
             of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)" 
             using lhs by simp
  then have "(\<Sum>j \<in> {4..<m}. ((\<Sum>h \<in> {0..<m}. of_int(N $$ (m-h-1,m-j-1)) * x $$ (m-h-1,0)) +
             (\<Sum>h \<in> {m..<\<v>}. of_int(N $$ (h,m-j-1)) * x $$ (h,0)))^2) =
             of_int \<Lambda> * (\<Sum>j \<in> {0..<\<v>}.(x $$ (j, 0)))^2 +
             of_int (\<k> - \<Lambda>) * (\<Sum>j \<in> {4..<m}. (x $$ (m-j-1, 0))^2)"
    using first_fact by simp
  thus ?thesis by simp
qed

end