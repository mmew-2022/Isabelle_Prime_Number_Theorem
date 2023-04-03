theory pnt_3
imports
  "pnt.pnt_2"
begin

lemma eventually_le_imp_bigo:
  assumes "\<forall>\<^sub>F x in F. ║f x║ \<le> g x"
  shows "f \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. ║f x║ \<le> 1 * ║g x║" by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma eventually_le_imp_bigo':
  assumes "\<forall>\<^sub>F x in F. ║f x║ \<le> g x"
  shows "(\<lambda>x. ║f x║) \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. ║║f x║║ \<le> 1 * ║g x║"
    by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma le_imp_bigo:
  assumes "\<And>x. ║f x║ \<le> g x"
  shows "f \<in> O[F](g)"
  by (intro eventually_le_imp_bigo eventuallyI assms)

lemma le_imp_bigo':
  assumes "\<And>x. ║f x║ \<le> g x"
  shows "(\<lambda>x. ║f x║) \<in> O[F](g)"
  by (intro eventually_le_imp_bigo' eventuallyI assms)

lemma zeta_div_bound':
  assumes "1 + exp (- 5 * ln (17 + 4 * t)) \<le> \<sigma>"
    and "13 / 22 \<le> t"
    and "z \<in> cball (\<complex> \<sigma> t) (1 / 2)"
  shows "║\<zeta> z / \<zeta> (\<complex> \<sigma> t)║ \<le> exp (15 * ln (17 + 4 * t))"
proof -
  interpret z: \<zeta>_bound_param_2
    "\<lambda>t. 1 / 2" "\<lambda>t. if 0 \<le> t then 5 * ln (15 + 2 * t) else 5 * ln 15" t \<sigma> t
    unfolding \<zeta>_bound_param_1_def \<zeta>_bound_param_2_def
              \<zeta>_bound_param_1_axioms_def \<zeta>_bound_param_2_axioms_def
    by (safe, rule zeta_bound_params.\<zeta>_bound_param_axioms)
       (use assms in auto)
  show ?thesis using z.zeta_div_bound assms(2) assms(3)
    unfolding z.s_def z.r_def by auto
qed

lemma zeta_div_bound:
  assumes "1 + exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> \<sigma>"
    and "13 / 22 \<le> \<bar>t\<bar>"
    and "z \<in> cball (\<complex> \<sigma> t) (1 / 2)"
  shows "║\<zeta> z / \<zeta> (\<complex> \<sigma> t)║ \<le> exp (15 * ln (17 + 4 * \<bar>t\<bar>))"
proof (cases "0 \<le> t")
  case True with assms(2) have "13 / 22 \<le> t" by auto
  thus ?thesis using assms by (auto intro: zeta_div_bound')
next
  case False with assms(2) have Ht: "t \<le> - 13 / 22" by auto
  moreover have 1: "\<complex> \<sigma> (- t) = cnj (\<complex> \<sigma> t)" by (auto simp add: legacy_Complex_simps)
  ultimately have "║\<zeta> (cnj z) / \<zeta> (\<complex> \<sigma> (- t))║ \<le> exp (15 * ln (17 + 4 * (- t)))"
    using assms(1) assms(3)
    by (intro zeta_div_bound', auto simp add: dist_complex_def)
       (subst complex_cnj_diff [symmetric], subst complex_mod_cnj)
  thus ?thesis using Ht by (subst (asm) 1) (simp add: norm_divide)
qed

definition C\<^sub>2 where "C\<^sub>2 \<equiv> 781200000 :: \<real>"
lemma C\<^sub>1_gt_zero: "0 < C\<^sub>1" unfolding C\<^sub>1_def by auto
lemma C\<^sub>2_gt_zero: "0 < C\<^sub>2" unfolding C\<^sub>2_def by auto

lemma logderiv_zeta_order_estimate':
"\<forall>\<^sub>F t in (abs going_to +\<infinity>).
  \<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
  \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
proof -
  define F where "F :: \<real> filter \<equiv> abs going_to +\<infinity>"
  define r where "r t \<equiv> ln (\<bar>t\<bar> + 3)" for t :: \<real>
  define s where "s \<sigma> t \<equiv> \<complex> (\<sigma> + 2 / 7 * C\<^sub>1 / r t) t" for \<sigma> t
  have r_ge_zero: "0 \<le> r t" for t unfolding r_def by auto
  have "║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
    when h: "1 - 1 / 7 * C\<^sub>1 / r t \<le> \<sigma>"
            "exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * C\<^sub>1 / r t"
            "8 / 7 * C\<^sub>1 / r t \<le> \<bar>t\<bar>"
            "8 / 7 * C\<^sub>1 / r t \<le> 1 / 2"
            "13 / 22 \<le> \<bar>t\<bar>" for \<sigma> t
  proof -
    have "║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> 8 * (15 * ln (17 + 4 * \<bar>t\<bar>)) / (8 / 7 * C\<^sub>1 / r t)"
    proof (rule lemma_3_9_beta1' [where ?s = "s \<sigma> t"], goal_cases)
      case 1 show ?case unfolding C\<^sub>1_def r_def by auto
      case 2 show ?case by auto
      have notin_ball: "1 \<notin> ball (s \<sigma> t) (8 / 7 * C\<^sub>1 / r t)"
      proof -
        note h(3)
        also have "\<bar>t\<bar> = \<bar>Im (\<complex> (\<sigma> + 2 / 7 * C\<^sub>1 / r t) t - 1)\<bar>" by auto
        also have "\<dots> \<le> ║\<complex> (\<sigma> + 2 / 7 * C\<^sub>1 / r t) t - 1║" by (rule abs_Im_le_cmod)
        finally show ?thesis
          unfolding s_def by (auto simp add: dist_complex_def)
      qed
      case 3 show ?case by (intro holomorphic_zeta notin_ball)
      case 6 show ?case
        using C\<^sub>1_gt_zero r_ge_zero unfolding s_def
        by (auto simp add: dist_complex_def legacy_Complex_simps)
      fix z assume Hz: "z \<in> ball (s \<sigma> t) (8 / 7 * C\<^sub>1 / r t)"
      show "\<zeta> z \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> \<zeta> z \<noteq> 0"
        hence zero: "\<zeta> (\<complex> (Re z) (Im z)) = 0" by auto
        have "C\<^sub>1 / r t \<le> C\<^sub>1 / ln (\<bar>Im z\<bar> + 2)"
        proof -
          have "║s \<sigma> t - z║ < 1"
            using Hz h(4) by (auto simp add: dist_complex_def)
          hence "\<bar>t - Im z\<bar> < 1"
            using abs_Im_le_cmod [of "s \<sigma> t - z"]
            unfolding s_def by (auto simp add: legacy_Complex_simps)
          hence "\<bar>Im z\<bar> < \<bar>t\<bar> + 1" by auto
          thus ?thesis unfolding r_def
            by (intro divide_left_mono mult_pos_pos)
               (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
        qed
        also have "\<dots> \<le> 1 - Re z"
          using notin_ball Hz by (intro zeta_nonzero_region zero) auto
        also have "\<dots> < 1 - Re (s \<sigma> t) + 8 / 7 * C\<^sub>1 / r t"
        proof -
          have "\<bar>Re (s \<sigma> t - z)\<bar> < 8 / 7 * C\<^sub>1 / r t"
            using Hz abs_Re_le_cmod [of "s \<sigma> t - z"]
            by (auto simp add: dist_complex_def)
          thus ?thesis by auto
        qed
        also have "\<dots> = 1 - \<sigma> + 6 / 7 * C\<^sub>1 / r t" unfolding s_def by auto
        also have "\<dots> \<le> C\<^sub>1 / r t" using h(1) by auto
        finally show False by auto
      qed
      from Hz have "z \<in> cball (s \<sigma> t) (1 / 2)"
        using h(4) by auto
      thus "║\<zeta> z / \<zeta> (s \<sigma> t)║ \<le> exp (15 * ln (17 + 4 * \<bar>t\<bar>))"
        using h(1) h(2) unfolding s_def
        by (intro zeta_div_bound h(5)) auto
    qed
    also have "\<dots> = 105 / C\<^sub>1 * ln (17 + 4 * \<bar>t\<bar>) * r t"
      by (auto simp add: field_simps)
    also have "\<dots> \<le> 525 / C\<^sub>1 * ln (\<bar>t\<bar> + 2) * ln (\<bar>t\<bar> + 3)"
    proof -
      have "105 / C\<^sub>1 * ln (17 + 4 * \<bar>t\<bar>) * r t \<le> 105 / C\<^sub>1 * (5 * ln (\<bar>t\<bar> + 2)) * r t"
        by (intro mult_left_mono mult_right_mono ln_bound_1)
           (unfold r_def, use C\<^sub>1_gt_zero in auto)
      thus ?thesis unfolding r_def by auto
    qed
    also have "\<dots> \<le> 525 / C\<^sub>1 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
      unfolding power2_eq_square
      by (simp add: mult_ac, intro divide_right_mono mult_right_mono)
         (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
    also have "\<dots> = C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2" unfolding C\<^sub>1_def C\<^sub>2_def by auto
    finally show ?thesis .
  qed
  hence
    "\<forall>\<^sub>F t in F.
        exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * C\<^sub>1 / r t
    \<longrightarrow> 8 / 7 * C\<^sub>1 / r t \<le> \<bar>t\<bar>
    \<longrightarrow> 8 / 7 * C\<^sub>1 / r t \<le> 1 / 2
    \<longrightarrow> 13 / 22 \<le> \<bar>t\<bar>
    \<longrightarrow> (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / r t \<le> \<sigma>
      \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by (rule_tac eventuallyI) blast
  moreover have "\<forall>\<^sub>F t in F. exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * C\<^sub>1 / r t"
    unfolding F_def r_def by (rule eventually_going_toI) (unfold C\<^sub>1_def, real_asymp)
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * C\<^sub>1 / r t \<le> \<bar>t\<bar>"
    unfolding F_def r_def by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * C\<^sub>1 / r t \<le> 1 / 2"
    unfolding F_def r_def by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 13 / 22 \<le> \<bar>t\<bar>"
    unfolding F_def by (rule eventually_going_toI) real_asymp
  ultimately have
    "\<forall>\<^sub>F t in F. (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / r t \<le> \<sigma>
      \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by eventually_elim blast
  thus ?thesis unfolding F_def r_def .
qed

definition C\<^sub>3 where
"C\<^sub>3 \<equiv> SOME T. 0 < T \<and>
  (\<forall>t. T \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"

lemma C\<^sub>3_prop:
  "0 < C\<^sub>3 \<and>
  (\<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"
proof -
  obtain T' where hT:
  "\<And>t. T' \<le> \<bar>t\<bar> \<Longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    using logderiv_zeta_order_estimate'
      [unfolded going_to_def, THEN rev_iffD1,
      OF eventually_filtercomap_at_top_linorder] by blast
  define T where "T \<equiv> max 1 T'"
  show ?thesis unfolding C\<^sub>3_def
    by (rule someI [of _ T]) (unfold T_def, use hT in auto)
qed

lemma C\<^sub>3_gt_zero: "0 < C\<^sub>3" using C\<^sub>3_prop by blast

theorem logderiv_zeta_order_estimate:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>" "C\<^sub>3 \<le> \<bar>t\<bar>"
  shows "║L\<zeta>\<Zprime> (\<complex> \<sigma> t)║ \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
  using assms C\<^sub>3_prop by blast

definition \<zeta>\<^sub>0 where "\<zeta>\<^sub>0 s \<equiv> pre_zeta 1 s * (s - 1) + 1"

lemma \<zeta>\<^sub>0_analytic:
  "\<zeta>\<^sub>0 analytic_on UNIV"
  unfolding \<zeta>\<^sub>0_def by (intro analytic_intros) auto

lemma \<zeta>\<^sub>0_analytic_on [analytic_intros]:
  "\<zeta>\<^sub>0 analytic_on A" using \<zeta>\<^sub>0_analytic analytic_on_subset by auto

lemma \<zeta>\<^sub>0_holomorphic_on [holomorphic_intros]:
  "\<zeta>\<^sub>0 holomorphic_on A" using \<zeta>\<^sub>0_analytic_on by (intro analytic_imp_holomorphic)

lemma \<zeta>_eq_\<zeta>\<^sub>0:
  "\<zeta> s = \<zeta>\<^sub>0 s / (s - 1)"
proof (cases "s = 1")
  case True thus ?thesis using zeta_1 unfolding \<zeta>\<^sub>0_def by auto
next
  case False with zeta_pole_eq [OF this]
  show ?thesis unfolding \<zeta>\<^sub>0_def by (auto simp add: field_simps)
qed

lemma \<zeta>\<^sub>0_1 [simp]: "\<zeta>\<^sub>0 1 = 1" unfolding \<zeta>\<^sub>0_def by auto

lemma \<zeta>_eq_zero_iff_\<zeta>\<^sub>0:
  shows "s \<noteq> 1 \<Longrightarrow> \<zeta>\<^sub>0 s = 0 \<longleftrightarrow> \<zeta> s = 0"
  using \<zeta>_eq_\<zeta>\<^sub>0 [of s] by auto

lemma \<zeta>\<^sub>0_eq_zero_iff:
  shows "\<zeta>\<^sub>0 s = 0 \<longleftrightarrow> \<zeta> s = 0 \<and> s \<noteq> 1"
  by (cases "s = 1", use \<zeta>_eq_zero_iff_\<zeta>\<^sub>0 in auto)

lemma \<zeta>_eq_zero_iff:
  shows "\<zeta> s = 0 \<longleftrightarrow> \<zeta>\<^sub>0 s = 0 \<or> s = 1"
  by (subst \<zeta>\<^sub>0_eq_zero_iff, use zeta_1 in auto)

lemma logderiv_inverse:
  assumes "x \<noteq> 0"
  shows "logderiv (\<lambda>x. 1 / x) x = - 1 / x"
proof -
  have "deriv (\<lambda>x. 1 / x) x = (deriv (\<lambda>x. 1) x * x - 1 * deriv (\<lambda>x. x) x) / x\<^sup>2"
    by (rule deriv_divide) (use assms in auto)
  hence "deriv (\<lambda>x. 1 / x) x = - 1 / x\<^sup>2" by auto
  thus ?thesis unfolding logderiv_def power2_eq_square using assms by auto
qed

lemma logderiv_\<zeta>_eq_\<zeta>\<^sub>0:
  assumes "s \<noteq> 1" "\<zeta> s \<noteq> 0"
  shows "L\<zeta>\<Zprime> s = logderiv \<zeta>\<^sub>0 s - 1 / (s - 1)"
proof -
  have "L\<zeta>\<Zprime> s = logderiv (\<lambda>s. \<zeta>\<^sub>0 s * (1 / (s - 1))) s"
    using \<zeta>_eq_\<zeta>\<^sub>0 by auto metis
  also have "\<dots> = logderiv \<zeta>\<^sub>0 s + logderiv (\<lambda>s. 1 / (s - 1)) s"
  proof -
    have "\<zeta>\<^sub>0 s \<noteq> 0" using assms \<zeta>_eq_zero_iff_\<zeta>\<^sub>0 by auto
    hence "\<zeta>\<^sub>0 #l\<Zprime> s"
      unfolding log_differentiable_def
      by (intro conjI analytic_on_imp_differentiable_at)
         (rule \<zeta>\<^sub>0_analytic, auto)
    moreover have "(\<lambda>z. 1 / (z - 1)) #l\<Zprime> s"
      unfolding log_differentiable_def using assms(1)
      by (intro derivative_intros conjI, auto)
    ultimately show ?thesis using assms by (intro logderiv_mult(1))
  qed
  also have "logderiv (\<lambda>s. 1 / (- 1 + s)) s = logderiv (\<lambda>s. 1 / s) (- 1 + s)"
    by (rule logderiv_shift) (insert assms(1), auto intro: derivative_intros)
  moreover have "\<dots> = - 1 / (- 1 + s)"
    by (rule logderiv_inverse) (use assms(1) in auto)
  ultimately show ?thesis by auto
qed

theorem analytic_logderiv [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>s. logderiv f s) analytic_on A"
  using assms unfolding logderiv_def by (intro analytic_intros)

definition zeta_zerofree_region
  where "zeta_zerofree_region \<equiv> {s. s \<noteq> 1 \<and> 1 - C\<^sub>1 / ln (\<bar>Im s\<bar> + 2) < Re s}"
definition logderiv_zeta_region
  where "logderiv_zeta_region \<equiv> {s. C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>Im s\<bar> + 3) \<le> Re s}"
definition zeta_strip_region
  where "zeta_strip_region \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> \<bar>Im s\<bar> \<le> T}"
definition zeta_strip_region'
  where "zeta_strip_region' \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> \<bar>Im s\<bar> \<le> T}"

theorem strip_in_zerofree_region:
  assumes "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
  shows "zeta_strip_region \<sigma> T \<subseteq> zeta_zerofree_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region_def by auto
  from this(3) have "C\<^sub>1 / ln (T + 2) \<le> C\<^sub>1 / ln (\<bar>Im s\<bar> + 2)"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> zeta_zerofree_region" using Hs' assms unfolding zeta_zerofree_region_def by auto
qed

theorem strip_in_logderiv_zeta_region:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "zeta_strip_region' \<sigma> T \<subseteq> logderiv_zeta_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region' \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "C\<^sub>3 \<le> \<bar>Im s\<bar>" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region'_def by auto
  from this(4) have "C\<^sub>1 / (7 * ln (T + 3)) \<le> C\<^sub>1 / (7 * ln (\<bar>Im s\<bar> + 3))"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> logderiv_zeta_region" using Hs' assms unfolding logderiv_zeta_region_def by auto
qed

theorem strip_condition_imp:
  assumes "0 \<le> T" "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
proof -
  have "ln (T + 2) \<le> 7 * ln (T + 2)" using assms(1) by auto
  also have "\<dots> < 7 * ln (T + 3)" using assms(1) by auto
  finally have "C\<^sub>1 / (7 * ln (T + 3)) < C\<^sub>1 / ln (T + 2)"
    using C\<^sub>1_gt_zero assms(1) by (intro divide_strict_left_mono mult_pos_pos) auto
  thus ?thesis using assms(2) by auto
qed

theorem zeta_zerofree_region:
  assumes "s \<in> zeta_zerofree_region"
  shows "\<zeta> s \<noteq> 0"
  using zeta_nonzero_region [of "Re s" "Im s"] assms
  unfolding zeta_zerofree_region_def by auto

theorem logderiv_zeta_region_estimate:
  assumes "s \<in> logderiv_zeta_region"
  shows "║L\<zeta>\<Zprime> s║ \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
  using logderiv_zeta_order_estimate [of "Im s" "Re s"] assms
  unfolding logderiv_zeta_region_def by auto

definition C\<^sub>4_C\<^sub>5_prop where
"C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5 \<equiv>
  0 < C\<^sub>4 \<and> 0 < C\<^sub>5 \<and>
  (\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))) \<and>
  (\<forall>\<^sub>F x in +\<infinity>. (\<forall>t. \<bar>t\<bar> \<le> x
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2))"

lemma logderiv_zeta_bound_vertical':
  "\<exists>C\<^sub>4 C\<^sub>5. C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5"
proof -
  define K where "K \<equiv> cbox (\<complex> 0 (-C\<^sub>3)) (\<complex> 2 C\<^sub>3)"
  define \<Gamma> where "\<Gamma> \<equiv> {s \<in> K. \<zeta>\<^sub>0 s = 0}"
  have "\<zeta>\<^sub>0 not_zero_on K"
    unfolding not_zero_on_def K_def using C\<^sub>3_gt_zero
    by (intro bexI [where x = 2])
       (auto simp add: \<zeta>_eq_zero_iff_\<zeta>\<^sub>0 zeta_2 in_cbox_complex_iff)
  hence fin: "finite \<Gamma>"
    unfolding \<Gamma>_def K_def
    by (auto intro!: convex_connected analytic_compact_finite_zeros \<zeta>\<^sub>0_analytic)
  define \<alpha> where "\<alpha> \<equiv> if \<Gamma> = {} then 0 else (1 + Max (Re ` \<Gamma>)) / 2"
  define K' where "K' \<equiv> cbox (\<complex> \<alpha> (-C\<^sub>3)) (\<complex> 1 C\<^sub>3)"
  have H\<alpha>: "\<alpha> \<in> {0..<1}"
  proof (cases "\<Gamma> = {}")
    case True thus ?thesis unfolding \<alpha>_def by auto
  next
    case False hence h\<Gamma>: "\<Gamma> \<noteq> {}" .
    moreover have "Re a < 1" if Ha: "a \<in> \<Gamma>" for a
    proof (rule ccontr)
      assume "\<not> Re a < 1" hence "1 \<le> Re a" by auto
      hence "\<zeta>\<^sub>0 a \<noteq> 0" by (subst \<zeta>\<^sub>0_eq_zero_iff) (use zeta_Re_ge_1_nonzero in auto)
      thus False using Ha unfolding \<Gamma>_def by auto
    qed
    moreover have "\<exists>a\<in>\<Gamma>. 0 \<le> Re a"
    proof -
      from h\<Gamma> have "\<exists>a. a \<in> \<Gamma>" by auto
      moreover have "\<And>a. a \<in> \<Gamma> \<Longrightarrow> 0 \<le> Re a"
        unfolding \<Gamma>_def K_def by (auto simp add: in_cbox_complex_iff)
      ultimately show ?thesis by auto
    qed
    ultimately have "0 \<le> Max (Re ` \<Gamma>)" "Max (Re ` \<Gamma>) < 1"
      using fin by (auto simp add: Max_ge_iff)
    thus ?thesis unfolding \<alpha>_def using h\<Gamma> by auto
  qed
  have nonzero: "\<zeta>\<^sub>0 z \<noteq> 0" when "z \<in> K'" for z
  proof (rule ccontr)
    assume "\<not> \<zeta>\<^sub>0 z \<noteq> 0"
    moreover have "K' \<subseteq> K" unfolding K'_def K_def
      by (rule subset_box_imp) (insert H\<alpha>, simp add: Basis_complex_def)
    ultimately have Hz: "z \<in> \<Gamma>" unfolding \<Gamma>_def using that by auto
    hence "Re z \<le> Max (Re ` \<Gamma>)" using fin by (intro Max_ge) auto
    also have "\<dots> < \<alpha>"
    proof -
      from Hz have "\<Gamma> \<noteq> {}" by auto
      thus ?thesis using H\<alpha> unfolding \<alpha>_def by auto
    qed
    finally have "Re z < \<alpha>" .
    moreover from \<open>z \<in> K'\<close> have "\<alpha> \<le> Re z"
      unfolding K'_def by (simp add: in_cbox_complex_iff)
    ultimately show False by auto
  qed
  hence "logderiv \<zeta>\<^sub>0 analytic_on K'" by (intro analytic_intros)
  moreover have "compact K'" unfolding K'_def by auto
  ultimately have "bounded ((logderiv \<zeta>\<^sub>0) ` K')"
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on
        compact_imp_bounded compact_continuous_image)
  from this [THEN rev_iffD1, OF bounded_pos]
  obtain M where
    hM: "\<And>s. s \<in> K' \<Longrightarrow> ║logderiv \<zeta>\<^sub>0 s║ \<le> M" by auto
  have "(\<lambda>x :: \<real>. 7 * ln (\<bar>x\<bar> + 3)) \<in> O(\<lambda>x. ln x)" by real_asymp
  then obtain \<beta>' where
    H\<beta>': "\<forall>\<^sub>F x in +\<infinity>. ║7 * ln (\<bar>x\<bar> + 3) :: \<real>║ \<le> \<beta>' * ║ln x║"
    unfolding bigo_def by auto
  define \<beta> where "\<beta> \<equiv> max 1 \<beta>'"
  define C\<^sub>4 where "C\<^sub>4 \<equiv> C\<^sub>1 / \<beta>"
  have "(\<lambda>t. C\<^sub>2 * (ln (t + 3))\<^sup>2) \<in> O(\<lambda>x. (ln x)\<^sup>2)" using C\<^sub>2_gt_zero by real_asymp
  then obtain \<gamma> where
    H\<gamma>: "\<forall>\<^sub>F x in +\<infinity>. ║C\<^sub>2 * (ln (x + 3))\<^sup>2║ \<le> \<gamma> * ║(ln x)\<^sup>2║"
    unfolding bigo_def by auto
  define C\<^sub>5 where "C\<^sub>5 \<equiv> max 1 \<gamma>"
  have C\<^sub>4_gt_zero: "0 < C\<^sub>4" using C\<^sub>1_gt_zero unfolding C\<^sub>4_def \<beta>_def by auto
  have C\<^sub>5_gt_zero: "0 < C\<^sub>5" unfolding C\<^sub>5_def by auto
  have "\<forall>\<^sub>F x in +\<infinity>. \<gamma> * (ln x)\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI mult_right_mono) (unfold C\<^sub>5_def, auto)
  with H\<gamma> have hC\<^sub>5: "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by eventually_elim (use C\<^sub>2_gt_zero in auto)
  have ln_x: "\<forall>\<^sub>F x in +\<infinity>. (0 :: \<real>) < ln x" by real_asymp
  moreover have "C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
    when h: "║7 * ln (\<bar>x\<bar> + 3)║ \<le> \<beta>' * ║ln x║"
            "0 < ln x" "1 < x" for x
  proof -
    have "\<beta>' * ln x \<le> \<beta> * ln x"
      unfolding \<beta>_def by (intro mult_right_mono) (use h(2) in auto)
    hence "7 * ln (x + 3) \<le> \<beta> * ln x" using h by (smt (verit) real_norm_def)
    moreover have "0 < \<beta>" unfolding \<beta>_def by auto
    ultimately show "C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
      unfolding C\<^sub>4_def using C\<^sub>1_gt_zero h(3)
      by (auto intro!: divide_left_mono mult_pos_pos)
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>. 0 < ln x
    \<longrightarrow> 1 < x \<longrightarrow> ║7 * ln (\<bar>x\<bar> + 3)║ \<le> \<beta>' * ║ln x║
    \<longrightarrow> C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
    by (intro eventuallyI) blast
  moreover have x_gt_1: "\<forall>\<^sub>F x in +\<infinity>. (1 :: \<real>) < x" by auto
  ultimately have hC\<^sub>4: "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
    using ln_x H\<beta>' by eventually_elim blast
  moreover have
    "║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2"
    when h: "C\<^sub>3 \<le> \<bar>t\<bar>" "\<bar>t\<bar> \<le> x" "1 < x"
            "C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
            "C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2" for x t
  proof -
    have "Re (\<complex> (1 - C\<^sub>4 / ln x) t) \<noteq> Re 1" using C\<^sub>4_gt_zero h(3) by auto
    hence "\<complex> (1 - C\<^sub>4 / ln x) t \<noteq> 1" by metis
    hence "\<complex> (1 - C\<^sub>4 / ln x) t \<in> zeta_strip_region' (1 - C\<^sub>4 / ln x) x"
      unfolding zeta_strip_region'_def using h(1) h(2) by auto
    hence "║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>2 * (ln (\<bar>Im (\<complex> (1 - C\<^sub>4 / ln x) t)\<bar> + 3))\<^sup>2"
      by (intro logderiv_zeta_region_estimate, rule_tac set_mp)
         (rule strip_in_logderiv_zeta_region [where ?\<sigma> = "1 - C\<^sub>4 / ln x" and ?T = x], use h(4) in auto)
    also have "\<dots> \<le> C\<^sub>2 * (ln (x + 3))\<^sup>2"
      by (intro mult_left_mono, subst power2_le_iff_abs_le)
         (use C\<^sub>2_gt_zero h(2) h(3) in auto)
    also have "\<dots> \<le> C\<^sub>5 * (ln x)\<^sup>2" by (rule h(5))
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> 1 < x \<longrightarrow> C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))
    \<longrightarrow> C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI) blast
  hence 1: "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2"
    using x_gt_1 hC\<^sub>4 hC\<^sub>5 by eventually_elim blast
  define f where "f x \<equiv> 1 - C\<^sub>4 / ln x" for x
  define g where "g x t \<equiv> \<complex> (f x) t" for x t
  let ?P = "\<lambda>x t. ║L\<zeta>\<Zprime> (g x t)║ \<le> M + ln x / C\<^sub>4"
  have "\<alpha> < 1" using H\<alpha> by auto
  hence "\<forall>\<^sub>F x in +\<infinity>. \<alpha> \<le> f x" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  moreover have f_lt_1: "\<forall>\<^sub>F x in +\<infinity>. f x < 1" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  ultimately have "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> g x t \<in> K' - {1}"
    unfolding g_def K'_def by eventually_elim (auto simp add: in_cbox_complex_iff legacy_Complex_simps)
  moreover have "║L\<zeta>\<Zprime> (g x t)║ \<le> M + 1 / (1 - f x)"
    when h: "g x t \<in> K' - {1}" "f x < 1" for x t
  proof -
    from h(1) have ne_1: "g x t \<noteq> 1" by auto
    hence "║L\<zeta>\<Zprime> (g x t)║ = ║logderiv \<zeta>\<^sub>0 (g x t) - 1 / (g x t - 1)║"
      using h(1) nonzero
      by (subst logderiv_\<zeta>_eq_\<zeta>\<^sub>0)
         (auto simp add: \<zeta>_eq_zero_iff_\<zeta>\<^sub>0 [symmetric])
    also have "\<dots> \<le> ║logderiv \<zeta>\<^sub>0 (g x t)║ + ║1 / (g x t - 1)║" by (rule norm_triangle_ineq4)
    also have "\<dots> \<le> M + 1 / (1 - f x)"
    proof -
      have "║logderiv \<zeta>\<^sub>0 (g x t)║ \<le> M" using that by (auto intro: hM)
      moreover have "\<bar>Re (g x t - 1)\<bar> \<le> ║g x t - 1║" by (rule abs_Re_le_cmod)
      hence "║1 / (g x t - 1)║ \<le> 1 / (1 - f x)"
        using ne_1 h(2)
        by (auto simp add: norm_divide g_def
                 intro!: divide_left_mono mult_pos_pos)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. f x < 1
    \<longrightarrow> g x t \<in> K' - {1} 
    \<longrightarrow> ║L\<zeta>\<Zprime> (g x t)║ \<le> M + 1 / (1 - f x)" by auto
  ultimately have "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> ║L\<zeta>\<Zprime> (g x t)║ \<le> M + 1 / (1 - f x)"
    using f_lt_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> ║L\<zeta>\<Zprime> (g x t)║ \<le> M + ln x / C\<^sub>4" unfolding f_def by auto
  moreover have "\<forall>\<^sub>F x in +\<infinity>. M + ln x / C\<^sub>4 \<le> C\<^sub>5 * (ln x)\<^sup>2" using C\<^sub>4_gt_zero C\<^sub>5_gt_zero by real_asymp
  ultimately have 2: "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> ║L\<zeta>\<Zprime> (g x t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2" by eventually_elim auto
  show ?thesis
  proof (unfold C\<^sub>4_C\<^sub>5_prop_def, intro exI conjI)
    show "0 < C\<^sub>4" "0 < C\<^sub>5" by (rule C\<^sub>4_gt_zero C\<^sub>5_gt_zero)+
    show "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))" by (rule hC\<^sub>4)
    have "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<or> \<bar>t\<bar> \<le> C\<^sub>3"
      by (rule eventuallyI) auto
    with 1 2 show "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> x \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2"
      unfolding f_def g_def by eventually_elim blast
  qed
qed

definition C\<^sub>4 where "C\<^sub>4 \<equiv> SOME C\<^sub>4. \<exists>C\<^sub>5. C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5"
definition C\<^sub>5 where "C\<^sub>5 \<equiv> SOME C\<^sub>5. C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5"

theorem
  C\<^sub>4_gt_zero: "0 < C\<^sub>4" (is ?prop_1) and
  C\<^sub>5_gt_zero: "0 < C\<^sub>5" (is ?prop_2) and
  C\<^sub>4_bound: "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))" (is ?prop_3) and
  logderiv_zeta_bound_vertical:
    "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> x
      \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln x) t)║ \<le> C\<^sub>5 * (ln x)\<^sup>2" (is ?prop_4) 
proof -
  have "\<exists>C\<^sub>4 C\<^sub>5. C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5" by (rule logderiv_zeta_bound_vertical')
  hence "\<exists>C\<^sub>5. C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5" unfolding C\<^sub>4_def by (rule someI_ex)
  hence h: "C\<^sub>4_C\<^sub>5_prop C\<^sub>4 C\<^sub>5" unfolding C\<^sub>5_def by (rule someI_ex)
  thus ?prop_1 ?prop_2 ?prop_3 ?prop_4 unfolding C\<^sub>4_C\<^sub>5_prop_def by blast+
qed

theorem has_sum_imp_has_subsum:
  fixes x :: "'a :: {comm_monoid_add, t2_space}"
  assumes "has_sum f A x"
  shows "has_subsum f A x"
proof -
  have "(\<forall>\<^sub>F x in +\<infinity>. sum f ({..<x} \<inter> A) \<in> S)"
    when "open S" "x \<in> S" for S
  proof -
    have "\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S)"
      using assms unfolding has_sum_def tendsto_def .
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S" using that by auto
    then obtain X where hX: "finite X" "X \<subseteq> A"
      and hY: "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> sum f Y \<in> S"
      unfolding eventually_finite_subsets_at_top by metis
    define n where "n \<equiv> Max X + 1"
    show ?thesis
    proof (subst eventually_sequentially, standard, safe)
      fix m assume Hm: "n \<le> m"
      moreover have "x \<in> X \<Longrightarrow> x < n" for x
        unfolding n_def using Max_ge [OF hX(1), of x] by auto
      ultimately show "sum f ({..<m} \<inter> A) \<in> S"
        using hX(2) by (intro hY, auto) (metis order.strict_trans2)
    qed
  qed
  thus ?thesis unfolding has_subsum_def sums_def tendsto_def
    by (simp add: sum.inter_restrict [symmetric])
qed

lemma nat_le_self: "0 \<le> x \<Longrightarrow> nat (int x) \<le> x" by auto
lemma floor_le: "\<And>x :: \<real>. \<lfloor>x\<rfloor> \<le> x" by auto
lemma ceil_ge: "\<And>x :: \<real>. x \<le> \<lceil>x\<rceil>" by auto

lemma norm_fds_mangoldt_complex:
  "\<And>n. ║d\<^sub>n (fds \<Lambda>) n║ = \<Lambda>\<^sub>r n" by (simp add: fds_nth_fds)

lemma analytic_on_powr_right [analytic_intros]:
  assumes "f analytic_on s"
  shows "(\<lambda>z. w ᣔ f z) analytic_on s"
proof (cases "w = 0")
  case False
  with assms show ?thesis
    unfolding analytic_on_def holomorphic_on_def field_differentiable_def
    by (metis (full_types) DERIV_chain' has_field_derivative_powr_right)
qed simp

locale prime_number_theorem =
  fixes c :: \<real>
  assumes Hc : "0 < c" and Hc': "c\<^sup>2 < 3 * C\<^sub>4"
begin

notation primes_psi ("\<psi>")
definition H where "H x \<equiv> exp (c / 2 * \<surd> (ln x))" for x :: \<real>
definition T where "T x \<equiv> exp (c * \<surd> (ln x))" for x :: \<real>
definition a where "a x \<equiv> 1 - C\<^sub>4 / (c * \<surd> (ln x))" for x :: \<real>
definition b where "b x \<equiv> 1 + 1 / (ln x)" for x :: \<real>
definition B where "B x \<equiv> 5 / 4 * ln x" for x :: \<real>
definition f where "f x s \<equiv> x ᣔ s / s * L\<zeta>\<Zprime> s" for x :: \<real> and s :: \<complex>
definition R where "R x \<equiv>
  x ᣔ (b x) * H x * B x / T x + 3 * (2 + ln (T x / b x))
  * (\<Sum>n | x - x / H x \<le> n \<and> n \<le> x + x / H x. ║d\<^sub>n (fds \<Lambda>) n║)" for x :: \<real>
definition z\<^sub>1 where "z\<^sub>1 x \<equiv> \<complex> (a x) (- T x)" for x
definition z\<^sub>2 where "z\<^sub>2 x \<equiv> \<complex> (b x) (- T x)" for x
definition z\<^sub>3 where "z\<^sub>3 x \<equiv> \<complex> (b x) (T x)" for x
definition z\<^sub>4 where "z\<^sub>4 x \<equiv> \<complex> (a x) (T x)" for x
definition rect where "rect x \<equiv> cbox (z\<^sub>1 x) (z\<^sub>3 x)" for x
definition rect' where "rect' x \<equiv> rect x - {1}" for x
definition P\<^sub>t where "P\<^sub>t x t \<equiv> linepath (\<complex> (a x) t) (\<complex> (b x) t)" for x t
definition P\<^sub>1 where "P\<^sub>1 x \<equiv> linepath (z\<^sub>1 x) (z\<^sub>4 x)" for x
definition P\<^sub>2 where "P\<^sub>2 x \<equiv> linepath (z\<^sub>2 x) (z\<^sub>3 x)" for x
definition P\<^sub>3 where "P\<^sub>3 x \<equiv> P\<^sub>t x (- T x)" for x
definition P\<^sub>4 where "P\<^sub>4 x \<equiv> P\<^sub>t x (T x)" for x
definition P\<^sub>r where "P\<^sub>r x \<equiv> rectpath (z\<^sub>1 x) (z\<^sub>3 x)" for x

lemma residue_f:
  "residue (f x) 1 = - x"
proof -
  define A where "A \<equiv> box (\<complex> 0 (- 1 / 2)) (\<complex> 2 (1 / 2))"
  have hA: "0 \<notin> A" "1 \<in> A" "open A"
    unfolding A_def by (auto simp add: mem_box Basis_complex_def)
  have "\<zeta>\<^sub>0 s \<noteq> 0" when "s \<in> A" for s
  proof -
    have "s \<noteq> 1 \<Longrightarrow> \<zeta> s \<noteq> 0"
      using that unfolding A_def
      by (intro zeta_nonzero_small_imag)
         (auto simp add: mem_box Basis_complex_def)
    thus ?thesis by (subst \<zeta>\<^sub>0_eq_zero_iff) auto
  qed
  hence h: "(\<lambda>s. x ᣔ s / s * logderiv \<zeta>\<^sub>0 s) holomorphic_on A"
    by (intro holomorphic_intros) (use hA in auto)
  have h': "(\<lambda>s. x ᣔ s / (s * (s - 1))) holomorphic_on A - {1}"
    by (auto intro!: holomorphic_intros) (use hA in auto)
  have s_ne_1: "\<forall>\<^sub>F s :: \<complex> in at 1. s \<noteq> 1"
    by (subst eventually_at_filter) auto
  moreover have "\<forall>\<^sub>F s in at 1. \<zeta> s \<noteq> 0"
    by (intro non_zero_neighbour_pole is_pole_zeta)
  ultimately have "\<forall>\<^sub>F s in at 1. L\<zeta>\<Zprime> s = logderiv \<zeta>\<^sub>0 s - 1 / (s - 1)"
    by eventually_elim (rule logderiv_\<zeta>_eq_\<zeta>\<^sub>0)
  moreover have
    "f x s = x ᣔ s / s * logderiv \<zeta>\<^sub>0 s - x ᣔ s / s / (s - 1)"
    when "L\<zeta>\<Zprime> s = logderiv \<zeta>\<^sub>0 s - 1 / (s - 1)" "s \<noteq> 0" "s \<noteq> 1" for s :: \<complex>
    unfolding f_def by (subst that(1)) (insert that, auto simp add: field_simps)
  hence "\<forall>\<^sub>F s :: \<complex> in at 1. s \<noteq> 0 \<longrightarrow> s \<noteq> 1
    \<longrightarrow> L\<zeta>\<Zprime> s = logderiv \<zeta>\<^sub>0 s - 1 / (s - 1)
    \<longrightarrow> f x s = x ᣔ s / s * logderiv \<zeta>\<^sub>0 s - x ᣔ s / s / (s - 1)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F s :: \<complex> in at 1. s \<noteq> 0"
    by (subst eventually_at_topological)
       (intro exI [of _ "UNIV - {0}"], auto)
  ultimately have "\<forall>\<^sub>F s :: \<complex> in at 1. f x s = x ᣔ s / s * logderiv \<zeta>\<^sub>0 s - x ᣔ s / s / (s - 1)"
    using s_ne_1 by eventually_elim blast
  hence "residue (f x) 1 = residue (\<lambda>s. x ᣔ s / s * logderiv \<zeta>\<^sub>0 s - x ᣔ s / s / (s - 1)) 1"
    by (intro residue_cong refl)
  also have "\<dots> = residue (\<lambda>s. x ᣔ s / s * logderiv \<zeta>\<^sub>0 s) 1 - residue (\<lambda>s. x ᣔ s / s / (s - 1)) 1"
    by (subst residue_diff [where ?s = A]) (use h h' hA in auto)
  also have "\<dots> = - x"
  proof -
    have "residue (\<lambda>s. x ᣔ s / s * logderiv \<zeta>\<^sub>0 s) 1 = 0"
      by (rule residue_holo [where ?s = A]) (use hA h in auto)
    moreover have "residue (\<lambda>s. x ᣔ s / s / (s - 1)) 1 = (x :: \<complex>) ᣔ 1 / 1"
      by (rule residue_simple [where ?s = A]) (use hA in \<open>auto intro!: holomorphic_intros\<close>)
    ultimately show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma rect_in_strip:
  "rect x - {1} \<subseteq> zeta_strip_region (a x) (T x)"
  unfolding rect_def zeta_strip_region_def z\<^sub>1_def z\<^sub>3_def
  by (auto simp add: in_cbox_complex_iff)

lemma rect_in_strip':
  "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> zeta_strip_region' (a x) (T x)"
  unfolding rect_def zeta_strip_region'_def z\<^sub>1_def z\<^sub>3_def
  using C\<^sub>3_gt_zero by (auto simp add: in_cbox_complex_iff)

lemma
  rect'_in_zerofree: "\<forall>\<^sub>F x in +\<infinity>. rect' x \<subseteq> zeta_zerofree_region" and
  rect_in_logderiv_zeta: "\<forall>\<^sub>F x in +\<infinity>. {s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
proof (goal_cases)
  case 1 have
    "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))" by (rule C\<^sub>4_bound)
  moreover have "LIM x +\<infinity>. exp (c * \<surd> (ln x)) :> +\<infinity>" using Hc by real_asymp
  ultimately have h:
   "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / ln (exp (c * \<surd> (ln x)))
    \<le> C\<^sub>1 / (7 * ln (exp (c * \<surd> (ln x)) + 3))" (is "eventually ?P _")
    by (rule eventually_compose_filterlim)
  moreover have
    "?P x \<Longrightarrow> zeta_strip_region (a x) (T x) \<subseteq> zeta_zerofree_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_zerofree_region strip_condition_imp) auto
  hence "\<forall>\<^sub>F x in +\<infinity>. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  ultimately show ?case unfolding rect'_def by eventually_elim (use rect_in_strip in auto)
  case 2 from h have
    "?P x \<Longrightarrow> zeta_strip_region' (a x) (T x) \<subseteq> logderiv_zeta_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_logderiv_zeta_region) auto
  hence "\<forall>\<^sub>F x in +\<infinity>. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  thus ?case using h by eventually_elim (use rect_in_strip' in auto)
qed

lemma zeta_nonzero_in_rect:
  "\<forall>\<^sub>F x in +\<infinity>. \<forall>s. s \<in> rect' x \<longrightarrow> \<zeta> s \<noteq> 0"
  using rect'_in_zerofree by eventually_elim (use zeta_zerofree_region in auto)

lemma zero_notin_rect: "\<forall>\<^sub>F x in +\<infinity>. 0 \<notin> rect' x"
proof -
  have "\<forall>\<^sub>F x in +\<infinity>. C\<^sub>4 / (c * \<surd> (ln x)) < 1"
    using Hc by real_asymp
  thus ?thesis
    unfolding rect'_def rect_def z\<^sub>1_def z\<^sub>4_def T_def a_def
    by eventually_elim (simp add: in_cbox_complex_iff)
qed

lemma f_analytic:
  "\<forall>\<^sub>F x in +\<infinity>. f x analytic_on rect' x"
  using zeta_nonzero_in_rect zero_notin_rect unfolding f_def
  by eventually_elim (intro analytic_intros, auto, simp add: rect'_def)

lemma path_image_in_rect_1:
  assumes "0 \<le> T x \<and> a x \<le> b x"
  shows "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
  unfolding P\<^sub>1_def P\<^sub>2_def rect_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

lemma path_image_in_rect_2:
  assumes "0 \<le> T x \<and> a x \<le> b x \<and> t \<in> {-T x..T x}"
  shows "path_image (P\<^sub>t x t) \<subseteq> rect x"
  unfolding P\<^sub>t_def rect_def z\<^sub>1_def z\<^sub>3_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

definition path_in_rect' where
"path_in_rect' x \<equiv>
  path_image (P\<^sub>1 x) \<subseteq> rect' x \<and> path_image (P\<^sub>2 x) \<subseteq> rect' x \<and>
  path_image (P\<^sub>3 x) \<subseteq> rect' x \<and> path_image (P\<^sub>4 x) \<subseteq> rect' x"

lemma path_image_in_rect':
  assumes "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "path_in_rect' x"
proof -
  have "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
    by (rule path_image_in_rect_1) (use assms in auto)
  moreover have "path_image (P\<^sub>3 x) \<subseteq> rect x" "path_image (P\<^sub>4 x) \<subseteq> rect x"
    unfolding P\<^sub>3_def P\<^sub>4_def
    by (intro path_image_in_rect_2, (use assms in auto)[1])+
  moreover have
    "1 \<notin> path_image (P\<^sub>1 x) \<and> 1 \<notin> path_image (P\<^sub>2 x) \<and>
     1 \<notin> path_image (P\<^sub>3 x) \<and> 1 \<notin> path_image (P\<^sub>4 x)"
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def using assms
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  ultimately show ?thesis unfolding path_in_rect'_def rect'_def by blast
qed

lemma asymp_1:
  "\<forall>\<^sub>F x in +\<infinity>. 0 < T x \<and> a x < 1 \<and> 1 < b x"
  unfolding T_def a_def b_def
  by (intro eventually_conj, insert Hc C\<^sub>4_gt_zero) (real_asymp)+

lemma f_continuous_on:
  "\<forall>\<^sub>F x in +\<infinity>. \<forall>A\<subseteq>rect' x. continuous_on A (f x)"
  using f_analytic
  by (eventually_elim, safe)
     (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic,
      elim analytic_on_subset)

lemma contour_integrability:
  "\<forall>\<^sub>F x in +\<infinity>. f x \<llangle>~\<integral>\<rrangle> P\<^sub>1 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>2 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>3 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>4 x"
proof -
  have "\<forall>\<^sub>F x in +\<infinity>. path_in_rect' x"
    using asymp_1 by eventually_elim (rule path_image_in_rect')
  thus ?thesis using f_continuous_on
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def path_in_rect'_def
    by eventually_elim
       (intro conjI contour_integrable_continuous_linepath,
        fold z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def, auto)
qed

lemma contour_integral_rectpath':
  assumes "f x analytic_on (rect' x)" "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "~\<integral> (P\<^sub>r x) (f x) = - 2 * \<pi> * \<i> * x"
proof -
  define z where "z \<equiv> (1 + b x) / 2"
  have Hz: "z \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2)
    by (auto simp add: mem_box Basis_complex_def)
  have Hz': "z \<noteq> 1" unfolding z_def using assms(2) by auto
  have "connected (rect' x)"
  proof -
    have box_nonempty: "box (z\<^sub>1 x) (z\<^sub>3 x) \<noteq> {}" using Hz by auto
    hence "aff_dim (closure (box (z\<^sub>1 x) (z\<^sub>3 x))) = 2"
      by (subst closure_aff_dim, subst aff_dim_open) auto
    thus ?thesis
      unfolding rect'_def using box_nonempty
      by (subst (asm) closure_box)
         (auto intro: connected_punctured_convex simp add: rect_def)
  qed
  moreover have Hz'': "z \<in> rect' x"
    unfolding rect'_def rect_def using box_subset_cbox Hz Hz' by auto
  ultimately obtain T where hT:
    "f x holomorphic_on T" "open T" "rect' x \<subseteq> T" "connected T"
    using analytic_on_holomorphic_connected assms(1) by (metis dual_order.refl)
  define U where "U \<equiv> T \<union> box (z\<^sub>1 x) (z\<^sub>3 x)"
  have one_in_box: "1 \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2) by (auto simp add: mem_box Basis_complex_def)
  have "~\<integral> (P\<^sub>r x) (f x) = 2 * \<pi> * \<i> *
    (\<Sum>s\<in>{1}. winding_number (P\<^sub>r x) s * residue (f x) s)"
  proof (rule Residue_theorem)
    show "finite {1}" "valid_path (P\<^sub>r x)" "pathfinish (P\<^sub>r x) = pathstart (P\<^sub>r x)"
      unfolding P\<^sub>r_def by auto
    show "open U" unfolding U_def using hT(2) by auto
    show "connected U" unfolding U_def
      by (intro connected_Un hT(4) convex_connected)
         (use Hz Hz'' hT(3) in auto)
    have "f x holomorphic_on box (z\<^sub>1 x) (z\<^sub>3 x) - {1}"
      by (rule holomorphic_on_subset, rule analytic_imp_holomorphic, rule assms(1))
         (unfold rect'_def rect_def, use box_subset_cbox in auto)
    hence "f x holomorphic_on ((T - {1}) \<union> (box (z\<^sub>1 x) (z\<^sub>3 x) - {1}))"
      by (intro holomorphic_on_Un) (use hT(1) hT(2) in auto)
    moreover have "\<dots> = U - {1}" unfolding U_def by auto
    ultimately show "f x holomorphic_on U - {1}" by auto
    have Hz: "Re (z\<^sub>1 x) \<le> Re (z\<^sub>3 x)" "Im (z\<^sub>1 x) \<le> Im (z\<^sub>3 x)"
      unfolding z\<^sub>1_def z\<^sub>3_def using assms(2) by auto
    have "path_image (P\<^sub>r x) = rect x - box (z\<^sub>1 x) (z\<^sub>3 x)"
      unfolding rect_def P\<^sub>r_def
      by (intro path_image_rectpath_cbox_minus_box Hz)
    thus "path_image (P\<^sub>r x) \<subseteq> U - {1}"
      using one_in_box hT(3) U_def unfolding rect'_def by auto
    have hU': "rect x \<subseteq> U"
      using hT(3) one_in_box unfolding U_def rect'_def by auto
    show "\<forall>z. z \<notin> U \<longrightarrow> winding_number (P\<^sub>r x) z = 0"
    proof (safe, goal_cases)
      case (1 z) thus ?case unfolding P\<^sub>r_def using hU'
        by (subst winding_number_rectpath_outside)
           (fold rect_def, auto intro: Hz)
    qed
  qed
  also have "\<dots> = - 2 * \<pi> * \<i> * x"
    unfolding P\<^sub>r_def by (simp add: residue_f, subst winding_number_rectpath, auto intro: one_in_box)
  finally show ?thesis .
qed

lemma contour_integral_rectpath:
  "\<forall>\<^sub>F x in +\<infinity>. ~\<integral> (P\<^sub>r x) (f x) = - 2 * \<pi> * \<i> * x"
  using f_analytic asymp_1 by eventually_elim (rule contour_integral_rectpath')

lemma valid_paths:
  "valid_path (P\<^sub>1 x)" "valid_path (P\<^sub>2 x)" "valid_path (P\<^sub>3 x)" "valid_path (P\<^sub>4 x)"
  unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def by auto

lemma integral_rectpath_split:
  assumes "f x \<llangle>~\<integral>\<rrangle> P\<^sub>1 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>2 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>3 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>4 x"
  shows "~\<integral> (P\<^sub>3 x) (f x) + ~\<integral> (P\<^sub>2 x) (f x) - ~\<integral> (P\<^sub>4 x) (f x) - ~\<integral> (P\<^sub>1 x) (f x) = ~\<integral> (P\<^sub>r x) (f x)"
proof -
  define Q\<^sub>1 where "Q\<^sub>1 \<equiv> linepath (z\<^sub>3 x) (z\<^sub>4 x)"
  define Q\<^sub>2 where "Q\<^sub>2 \<equiv> linepath (z\<^sub>4 x) (z\<^sub>1 x)"
  have Q_eq: "Q\<^sub>1 = reversepath (P\<^sub>4 x)" "Q\<^sub>2 = reversepath (P\<^sub>1 x)"
    unfolding Q\<^sub>1_def Q\<^sub>2_def P\<^sub>1_def P\<^sub>4_def P\<^sub>t_def by (fold z\<^sub>3_def z\<^sub>4_def) auto
  hence "~\<integral> Q\<^sub>1 (f x) = - ~\<integral> (P\<^sub>4 x) (f x)" "~\<integral> Q\<^sub>2 (f x) = - ~\<integral> (P\<^sub>1 x) (f x)"
    by (auto intro: contour_integral_reversepath valid_paths)
  moreover have "~\<integral> (P\<^sub>3 x +++ P\<^sub>2 x +++ Q\<^sub>1 +++ Q\<^sub>2) (f x)
       = ~\<integral> (P\<^sub>3 x) (f x) + ~\<integral> (P\<^sub>2 x) (f x) + ~\<integral> Q\<^sub>1 (f x) + ~\<integral> Q\<^sub>2 (f x)"
  proof -
    have 1: "pathfinish (P\<^sub>2 x) = pathstart (Q\<^sub>1 +++ Q\<^sub>2)" "pathfinish Q\<^sub>1 = pathstart Q\<^sub>2"
      unfolding P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def by auto
    have 2: "valid_path Q\<^sub>1" "valid_path Q\<^sub>2" unfolding Q\<^sub>1_def Q\<^sub>2_def by auto
    have 3: "f x \<llangle>~\<integral>\<rrangle> P\<^sub>1 x" "f x \<llangle>~\<integral>\<rrangle> P\<^sub>2 x" "f x \<llangle>~\<integral>\<rrangle> P\<^sub>3 x" "f x \<llangle>~\<integral>\<rrangle> P\<^sub>4 x" "f x \<llangle>~\<integral>\<rrangle> Q\<^sub>1" "f x \<llangle>~\<integral>\<rrangle> Q\<^sub>2"
      using assms by (auto simp add: Q_eq intro: contour_integrable_reversepath valid_paths)
    show ?thesis by (subst contour_integral_join |
      auto intro: valid_paths valid_path_join contour_integrable_joinI 1 2 3)+
  qed
  ultimately show ?thesis
    unfolding P\<^sub>r_def z\<^sub>1_def z\<^sub>3_def rectpath_def
    by (simp add: Let_def, fold P\<^sub>t_def P\<^sub>3_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def)
       (fold P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def, auto)
qed

lemma P\<^sub>2_eq:
  "\<forall>\<^sub>F x in +\<infinity>. ~\<integral> (P\<^sub>2 x) (f x) + 2 * \<pi> * \<i> * x = ~\<integral> (P\<^sub>1 x) (f x) - ~\<integral> (P\<^sub>3 x) (f x) + ~\<integral> (P\<^sub>4 x) (f x)"
proof -
  have "\<forall>\<^sub>F x in +\<infinity>. ~\<integral> (P\<^sub>3 x) (f x) + ~\<integral> (P\<^sub>2 x) (f x) - ~\<integral> (P\<^sub>4 x) (f x) - ~\<integral> (P\<^sub>1 x) (f x) = - 2 * \<pi> * \<i> * x"
    using contour_integrability contour_integral_rectpath asymp_1 f_analytic
    by eventually_elim (metis integral_rectpath_split)
  thus ?thesis by (auto simp add: field_simps)
qed

lemma estimation_P\<^sub>1:
  "(\<lambda>x. ║~\<integral> (P\<^sub>1 x) (f x)║) \<in> rem_est (c / 4) 1"
proof -
  define r where "r x \<equiv> C\<^sub>5 * (c * \<surd> (ln x))\<^sup>2 * x ᣔ a x * ln (1 + T x / a x)" for x
  note logderiv_zeta_bound_vertical
  moreover have "LIM x +\<infinity>. T x :> +\<infinity>"
    unfolding T_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (1 - C\<^sub>4 / ln (T x)) t)║ \<le> C\<^sub>5 * (ln (T x))\<^sup>2"
    unfolding a_def by (rule eventually_compose_filterlim)
  hence "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> ║L\<zeta>\<Zprime> (\<complex> (a x) t)║ \<le> C\<^sub>5 * (c * \<surd> (ln x))\<^sup>2"
    unfolding a_def T_def by auto
  moreover have "\<forall>\<^sub>F x in +\<infinity>. (f x) \<llangle>~\<integral>\<rrangle> (P\<^sub>1 x)"
    using contour_integrability by eventually_elim auto
  hence "\<forall>\<^sub>F x in +\<infinity>. (\<lambda>s. L\<zeta>\<Zprime> s * x ᣔ s / s) \<llangle>~\<integral>\<rrangle> (P\<^sub>1 x)"
     unfolding f_def by eventually_elim (auto simp add: field_simps)
  moreover have "\<forall>\<^sub>F x :: \<real> in +\<infinity>. 0 < x" by auto
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 0 < a x" unfolding a_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in +\<infinity>.
    ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>1 x) (\<lambda>s. L\<zeta>\<Zprime> s * x ᣔ s / s)║ \<le> r x"
    unfolding r_def P\<^sub>1_def z\<^sub>1_def z\<^sub>4_def using asymp_1
    by eventually_elim (rule perron_aux_3', auto)
  hence "\<forall>\<^sub>F x in +\<infinity>. ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>1 x) (f x)║ \<le> r x"
    unfolding f_def by eventually_elim (auto simp add: mult_ac)
  hence "(\<lambda>x. ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>1 x) (f x)║) \<in> O(r)"
    unfolding f_def by (rule eventually_le_imp_bigo')
  moreover have "r \<in> rem_est (c / 4) 1"
  proof -
    define r\<^sub>1 where "r\<^sub>1 x \<equiv> C\<^sub>5 * c\<^sup>2 * ln x * ln (1 + T x / a x)" for x
    define r\<^sub>2 where "r\<^sub>2 x \<equiv> exp (a x * ln x)" for x
    have ln_gt_0: "\<forall>\<^sub>F x :: \<real> in +\<infinity>. 0 < ln x" by real_asymp
    have x_gt_0: "\<forall>\<^sub>F x :: \<real> in +\<infinity>. 0 < x" by auto
    have "r\<^sub>1 \<in> O(\<lambda>x. (ln x)\<^sup>2)"
      unfolding r\<^sub>1_def T_def a_def using Hc C\<^sub>5_gt_zero by real_asymp
    moreover have "r\<^sub>2 \<in> O(\<lambda>x. x * exp (- (c / 3) * \<surd> (ln x)))"
    proof -
      have 1: "║r\<^sub>2 x║ \<le> x * exp (- (c / 3) * \<surd> (ln x))"
        when h: "0 < x" "0 < ln x" for x
      proof -
        have "a x * ln x = ln x + - C\<^sub>4 / c * \<surd> (ln x)" unfolding a_def
          using h(2) by (auto simp add: field_simps) (subst frac_eq_eq, use Hc in auto)
        hence "r\<^sub>2 x = exp (\<dots>)" unfolding r\<^sub>2_def by blast
        also have "\<dots> = x * exp (- C\<^sub>4 / c * \<surd> (ln x))"
          by (subst exp_add) (use h(1) in auto)
        also have "\<dots> \<le> x * exp (- (c / 3) * \<surd> (ln x))"
          by (intro mult_left_mono, subst exp_le_cancel_iff, intro mult_right_mono)
             (insert Hc Hc' h, auto simp add: power2_eq_square field_simps)
        finally show ?thesis unfolding r\<^sub>2_def by auto
      qed
      have "\<forall>\<^sub>F x in +\<infinity>. ║r\<^sub>2 x║ \<le> x * exp (- (c / 3) * \<surd> (ln x))"
        using ln_gt_0 x_gt_0 by eventually_elim (rule 1)
      thus ?thesis by (rule eventually_le_imp_bigo)
    qed
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x)
      \<in> O(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 3) * \<surd> (ln x))))"
      by (rule landau_o.big.mult)
    also have "(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 3) * \<surd> (ln x)))) \<in> rem_est (c / 4) 1"
      unfolding rem_est_def using Hc by real_asymp
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x) \<in> rem_est (c / 4) 1"
      unfolding rem_est_def by (rule landau_o.big_trans)
    moreover have "\<forall>\<^sub>F x in +\<infinity>. r x = r\<^sub>1 x * r\<^sub>2 x"
      using ln_gt_0 x_gt_0 unfolding r_def r\<^sub>1_def r\<^sub>2_def a_def
      by eventually_elim (unfold powr_def, auto simp add: field_simps)
    ultimately show ?thesis unfolding rem_est_def
      by (rule_tac landau_o.big.ev_eq_trans2)
  qed
  ultimately have "(\<lambda>x. ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>1 x) (f x)║) \<in> rem_est (c / 4) 1"
    unfolding rem_est_def by (rule landau_o.big_trans)
  thus ?thesis unfolding rem_est_def by (simp add: norm_divide)
qed

lemma estimation_P\<^sub>t':
  assumes h:
    "1 < x \<and> max 1 C\<^sub>3 \<le> T x" "a x < 1 \<and> 1 < b x"
    "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
    "f x \<llangle>~\<integral>\<rrangle> P\<^sub>3 x \<and> f x \<llangle>~\<integral>\<rrangle> P\<^sub>4 x"
    and Ht: "\<bar>t\<bar> = T x"
  shows "║~\<integral> (P\<^sub>t x t) (f x)║ \<le> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
proof -
  consider "t = T x" | "t = - T x" using Ht by fastforce
  hence "f x \<llangle>~\<integral>\<rrangle> P\<^sub>t x t"
    using Ht h(4) unfolding P\<^sub>t_def P\<^sub>3_def P\<^sub>4_def by cases auto
  moreover have "║f x s║ \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2)"
    when "s \<in> closed_segment (\<complex> (a x) t) (\<complex> (b x) t)" for s
  proof -
    have Hs: "s \<in> path_image (P\<^sub>t x t)" using that unfolding P\<^sub>t_def by auto
    have "path_image (P\<^sub>t x t) \<subseteq> rect x"
      by (rule path_image_in_rect_2) (use h(2) Ht in auto)
    moreover have Hs': "Re s \<le> b x" "Im s = t"
    proof -
      have "u \<le> 1 \<Longrightarrow> (1 - u) * a x \<le> (1 - u) * b x" for u
        using h(2) by (intro mult_left_mono) auto
      thus "Re s \<le> b x" "Im s = t"
        using that h(2) unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
    qed
    hence "C\<^sub>3 \<le> \<bar>Im s\<bar>" using h(1) Ht by auto
    ultimately have "s \<in> logderiv_zeta_region" using Hs h(3) by auto
    hence "║L\<zeta>\<Zprime> s║ \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
      by (rule logderiv_zeta_region_estimate)
    also have "\<dots> = C\<^sub>2 * (ln (T x + 3))\<^sup>2" using Hs'(2) Ht by auto
    also have "║x ᣔ s / s║ \<le> exp 1 * x / T x"
    proof -
      have "║x ᣔ s║ = Re x ᣔ Re s" using h(1) by (intro norm_powr_real_powr) auto
      also have "\<dots> = x ᣔ Re s" by auto
      also have "\<dots> \<le> x ᣔ b x" by (intro powr_mono Hs') (use h(1) in auto)
      also have "\<dots> = exp 1 * x"
        using h(1) unfolding powr_def b_def by (auto simp add: field_simps exp_add)
      finally have "║x ᣔ s║ \<le> exp 1 * x" .
      moreover have "T x \<le> ║s║" using abs_Im_le_cmod [of s] Hs'(2) h(1) Ht by auto
      hence 1: "║x ᣔ s║ / ║s║ \<le> ║x ᣔ s║ / T x"
        using h(1) by (intro divide_left_mono mult_pos_pos) auto
      ultimately have "\<dots> \<le> exp 1 * x / T x"
        by (intro divide_right_mono) (use h(1) in auto)
      thus ?thesis using 1 by (subst norm_divide) linarith
    qed
    ultimately show ?thesis unfolding f_def
      by (subst norm_mult, intro mult_mono, auto)
         (metis norm_ge_zero order.trans)
  qed
  ultimately have "║~\<integral> (P\<^sub>t x t) (f x)║
    \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2) * ║\<complex> (b x) t - \<complex> (a x) t║"
    unfolding P\<^sub>t_def
    by (intro contour_integral_bound_linepath)
       (use C\<^sub>2_gt_zero h(1) in auto)
  also have "\<dots> = C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
    using h(2) by (simp add: legacy_Complex_simps)
  finally show ?thesis .
qed

lemma estimation_P\<^sub>t:
  "(\<lambda>x. ║~\<integral> (P\<^sub>3 x) (f x)║) \<in> rem_est (c / 4) 1 \<and>
   (\<lambda>x. ║~\<integral> (P\<^sub>4 x) (f x)║) \<in> rem_est (c / 4) 1"
proof -
  define r where "r x \<equiv> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)" for x
  define p where "p x \<equiv> ║~\<integral> (P\<^sub>3 x) (f x)║ \<le> r x \<and> ║~\<integral> (P\<^sub>4 x) (f x)║ \<le> r x" for x
  have "\<forall>\<^sub>F x in +\<infinity>. 1 < x \<and> max 1 C\<^sub>3 \<le> T x"
    unfolding T_def by (rule eventually_conj) (simp, use Hc in real_asymp)
  hence "\<forall>\<^sub>F x in +\<infinity>. \<forall>t. \<bar>t\<bar> = T x \<longrightarrow> ║~\<integral> (P\<^sub>t x t) (f x)║ \<le> r x" (is "eventually ?P _")
    unfolding r_def using asymp_1 rect_in_logderiv_zeta contour_integrability
    by eventually_elim (use estimation_P\<^sub>t' in blast)
  moreover have "\<And>x. ?P x \<Longrightarrow> 0 < T x \<Longrightarrow> p x"
    unfolding p_def P\<^sub>3_def P\<^sub>4_def by auto
  hence "\<forall>\<^sub>F x in +\<infinity>. ?P x \<longrightarrow> 0 < T x \<longrightarrow> p x"
    by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in +\<infinity>. p x" using asymp_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in +\<infinity>.
    ║║~\<integral> (P\<^sub>3 x) (f x)║║ \<le> 1 * ║r x║ \<and>
    ║║~\<integral> (P\<^sub>4 x) (f x)║║ \<le> 1 * ║r x║"
    unfolding p_def by eventually_elim auto
  hence "(\<lambda>x. ║~\<integral> (P\<^sub>3 x) (f x)║) \<in> O(r) \<and> (\<lambda>x. ║~\<integral> (P\<^sub>4 x) (f x)║) \<in> O(r)"
    by (subst (asm) eventually_conj_iff, blast)+
  moreover have "r \<in> rem_est (c / 4) 1"
    unfolding r_def rem_est_def a_def b_def T_def using Hc by real_asymp
  ultimately show ?thesis
    unfolding rem_est_def using landau_o.big_trans by blast
qed

lemma Re_path_P\<^sub>2:
  "\<And>z. z \<in> path_image (P\<^sub>2 x) \<Longrightarrow> Re z = b x"
  unfolding P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

lemma estimation_P\<^sub>2:
  "(\<lambda>x. ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x) + x║) \<in> rem_est (c / 4) 1"
proof -
  define r where "r x \<equiv> ║~\<integral> (P\<^sub>1 x) (f x)║ + ║~\<integral> (P\<^sub>3 x) (f x)║ + ║~\<integral> (P\<^sub>4 x) (f x)║" for x
  have [simp]: "║a - b + c║ \<le> ║a║ + ║b║ + ║c║" for a b c
    using adhoc_norm_triangle norm_triangle_ineq4 by blast
  have "\<forall>\<^sub>F x in +\<infinity>. ║~\<integral> (P\<^sub>2 x) (f x) + 2 * \<pi> * \<i> * x║ \<le> r x"
    unfolding r_def using P\<^sub>2_eq by eventually_elim auto
  hence "(\<lambda>x. ║~\<integral> (P\<^sub>2 x) (f x) + 2 * \<pi> * \<i> * x║) \<in> O(r)"
    by (rule eventually_le_imp_bigo')
  moreover have "r \<in> rem_est (c / 4) 1"
    using estimation_P\<^sub>1 estimation_P\<^sub>t
    unfolding r_def rem_est_def by (intro sum_in_bigo) auto
  ultimately have "(\<lambda>x. ║~\<integral> (P\<^sub>2 x) (f x) + 2 * \<pi> * \<i> * x║) \<in> rem_est (c / 4) 1"
    unfolding rem_est_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. ║1 / (2 * \<pi> * \<i>) * (~\<integral> (P\<^sub>2 x) (f x) + 2 * \<pi> * \<i> * x)║) \<in> rem_est (c / 4) 1"
    unfolding rem_est_def by (auto simp add: norm_mult norm_divide)
  thus ?thesis by (auto simp add: algebra_simps)
qed

lemma estimation_R:
  "R \<in> rem_est (c / 4) 1"
proof -
  define \<Gamma> where "\<Gamma> x \<equiv> {n :: \<nat>. x - x / H x \<le> n \<and> n \<le> x + x / H x}" for x
  have 1: "(\<lambda>x. x ᣔ b x * H x * B x / T x) \<in> rem_est (c / 4) 1"
    unfolding b_def H_def B_def T_def rem_est_def using Hc by real_asymp
  have "║\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║║ \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    when h: "0 < x - x / H x" "0 < x / H x" "0 \<le> ln (x + x / H x)" for x
  proof -
    have "║\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║║ = (\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║)"
      by simp (subst abs_of_nonneg, auto intro: sum_nonneg)
    also have "\<dots> = sum \<Lambda>\<^sub>r (\<Gamma> x)"
      by (subst norm_fds_mangoldt_complex) (rule refl)
    also have "\<dots> \<le> card (\<Gamma> x) * ln (x + x / H x)"
    proof (rule sum_bounded_above)
      fix n assume "n \<in> \<Gamma> x"
      hence Hn: "0 < n" "n \<le> x + x / H x" unfolding \<Gamma>_def using h by auto
      hence "\<Lambda>\<^sub>r n \<le> ln n" by (intro mangoldt_le)
      also have "\<dots> \<le> ln (x + x / H x)" using Hn by auto
      finally show "\<Lambda>\<^sub>r n \<le> ln (x + x / H x)" .
    qed
    also have "\<dots> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    proof -
      have \<Gamma>_eq: "\<Gamma> x = {nat \<lceil>x - x / H x\<rceil>..<nat (\<lfloor>x + x / H x\<rfloor> + 1)}"
        unfolding \<Gamma>_def by (subst nat_le_real_iff) (subst nat_ceiling_le_eq [symmetric], auto)
      moreover have "nat (\<lfloor>x + x / H x\<rfloor> + 1) = \<lfloor>x + x / H x\<rfloor> + 1" using h(1) h(2) by auto
      moreover have "nat \<lceil>x - x / H x\<rceil> = \<lceil>x - x / H x\<rceil>" using h(1) by auto
      moreover have "\<lfloor>x + x / H x\<rfloor> \<le> x + x / H x" by (rule floor_le)
      moreover have "\<lceil>x - x / H x\<rceil> \<ge> x - x / H x" by (rule ceil_ge)
      ultimately have "(nat (\<lfloor>x + x / H x\<rfloor> + 1) :: \<real>) - nat \<lceil>x - x / H x\<rceil> \<le> 2 * x / H x + 1" by linarith
      hence "card (\<Gamma> x) \<le> 2 * x / H x + 1" using h(2) by (subst \<Gamma>_eq) (auto simp add: of_nat_diff_real)
      thus ?thesis using h(3) by (rule mult_right_mono)
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>.
    0 < x - x / H x \<longrightarrow> 0 < x / H x \<longrightarrow> 0 \<le> ln (x + x / H x)
    \<longrightarrow> ║\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║║ \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 0 < x - x / H x" unfolding H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 0 < x / H x" unfolding H_def  using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 0 \<le> ln (x + x / H x)" unfolding H_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in +\<infinity>. ║\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║║ \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by eventually_elim blast
  hence "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║) \<in> O(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x))"
    by (rule eventually_le_imp_bigo)
  moreover have "(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x)) \<in> rem_est (c / 3) 1"
    unfolding rem_est_def H_def using Hc by real_asymp
  ultimately have "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║) \<in> rem_est (c / 3) 1"
    unfolding rem_est_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║))
      \<in> O(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- c / 3 * (ln x) ᣔ (1 / 2))))"
    unfolding rem_est_def by (intro landau_o.big.mult_left) auto
  moreover have "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- c / 3 * (ln x) ᣔ (1 / 2)))) \<in> rem_est (c / 4) 1"
    unfolding rem_est_def T_def b_def using Hc by real_asymp
  ultimately have 2: "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. ║d\<^sub>n (fds \<Lambda>) n║)) \<in> rem_est (c / 4) 1"
    unfolding rem_est_def by (rule landau_o.big_trans)
  from 1 2 show ?thesis unfolding rem_est_def R_def \<Gamma>_def by (rule sum_in_bigo)
qed

lemma perron_psi:
  "\<forall>\<^sub>F x in +\<infinity>. ║\<psi> x + 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║ \<le> R x"
proof -
  have Hb: "\<forall>\<^sub>F x in +\<infinity>. 1 < b x" unfolding b_def by real_asymp
  hence "\<forall>\<^sub>F x in +\<infinity>. 0 < b x" by eventually_elim auto
  moreover have "\<forall>\<^sub>F x in +\<infinity>. b x \<le> T x" unfolding b_def T_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in +\<infinity>. abs_conv_abscissa (fds \<Lambda>) < ereal (b x)"
  proof -
    have "abs_conv_abscissa (fds \<Lambda>) \<le> 1" by (rule abs_conv_abscissa_mangoldt)
    hence "\<forall>\<^sub>F x in +\<infinity>. 1 < b x \<longrightarrow> abs_conv_abscissa (fds \<Lambda>) < ereal (b x)"
      by (rule_tac eventuallyI)
          (simp add: le_ereal_less one_ereal_def)
    thus ?thesis using Hb by (rule eventually_mp)
  qed
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 2 \<le> H x" unfolding H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in +\<infinity>. b x + 1 \<le> H x" unfolding b_def H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x :: \<real> in +\<infinity>. 2 \<le> x" by auto
  moreover have "\<forall>\<^sub>F x in +\<infinity>. (\<Sum>`n\<ge>1. ║d\<^sub>n (fds \<Lambda>) n║ / n \<nat>ᣔ b x) \<le> B x" (is "eventually ?P ?F")
  proof -
    have "?P x" when Hb: "1 < b x \<and> b x \<le> 23 / 20" for x
    proof -
      have "(\<Sum>`n\<ge>1. ║d\<^sub>n (fds \<Lambda>) n║ / n \<nat>ᣔ (b x)) = (\<Sum>`n\<ge>1. \<Lambda>\<^sub>r n / n \<nat>ᣔ (b x))"
        by (subst norm_fds_mangoldt_complex) (rule refl)
      also have "\<dots> = - Re (L\<zeta>\<Zprime> (b x))"
      proof -
        have "has_sum (\<lambda>n. \<Lambda>\<^sub>r n * n \<nat>ᣔ (-b x) * cos (0 * ln (real n)))
              {1..} (Re (- \<zeta>\<Zprime> (\<complex> (b x) 0) / \<zeta> (\<complex> (b x) 0)))"
          by (intro sums_Re_logderiv_zeta) (use Hb in auto)
        moreover have "\<complex> (b x) 0 = b x" by (rule complex_eqI) auto
        moreover have "Re (- \<zeta>\<Zprime> (b x) / \<zeta> (b x)) = - Re (L\<zeta>\<Zprime> (b x))"
          unfolding logderiv_def by auto
        ultimately have "has_sum (\<lambda>n. \<Lambda>\<^sub>r n * n \<nat>ᣔ (-b x)) {1..} (- Re (L\<zeta>\<Zprime> (b x)))"
          by auto
        hence "- Re (L\<zeta>\<Zprime> (b x)) = (\<Sum>`n\<ge>1. \<Lambda>\<^sub>r n * n \<nat>ᣔ (-b x))"
          by (intro has_sum_imp_has_subsum subsumI)
        also have "\<dots> = (\<Sum>`n\<ge>1. \<Lambda>\<^sub>r n / n \<nat>ᣔ (b x))"
          by (intro subsum_cong) (auto simp add: powr_minus_divide)
        finally show ?thesis by auto
      qed
      also have "\<dots> \<le> \<bar>Re (L\<zeta>\<Zprime> (b x))\<bar>" by auto
      also have "\<dots> \<le> ║L\<zeta>\<Zprime> (b x)║" by (rule abs_Re_le_cmod)
      also have "\<dots> \<le> 5 / 4 * (1 / (b x - 1))"
        by (rule logderiv_zeta_bound) (use Hb in auto)
      also have "\<dots> = B x" unfolding b_def B_def by auto
      finally show ?thesis .
    qed
    hence "\<forall>\<^sub>F x in +\<infinity>. 1 < b x \<and> b x \<le> 23 / 20 \<longrightarrow> ?P x" by auto
    moreover have "\<forall>\<^sub>F x in +\<infinity>. b x \<le> 23 / 20" unfolding b_def by real_asymp
    ultimately show ?thesis using Hb by eventually_elim auto
  qed
  ultimately have "\<forall>\<^sub>F x in +\<infinity>.
    ║sum_upto (d\<^sub>n (fds \<Lambda>)) x - 1 / (2 * \<pi> * \<i>)
      * ~\<integral> (P\<^sub>2 x) (\<lambda>s. eval_fds (fds \<Lambda>) s * x ᣔ s / s)║ \<le> R x"
    unfolding R_def P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
    by eventually_elim (rule perron_formula(2))
  moreover have "\<forall>\<^sub>F x in +\<infinity>. sum_upto (d\<^sub>n (fds \<Lambda>)) x = \<psi> x" for x
    unfolding primes_psi_def sum_upto_def by auto
  moreover have
     "~\<integral> (P\<^sub>2 x) (\<lambda>s. eval_fds (fds \<Lambda>) s * x ᣔ s / s)
    = ~\<integral> (P\<^sub>2 x) (\<lambda>s. - (x ᣔ s / s * L\<zeta>\<Zprime> s))"
    when "1 < b x" for x
  proof (rule contour_integral_eq, goal_cases)
    case (1 s)
    hence "Re s = b x" by (rule Re_path_P\<^sub>2)
    hence "eval_fds (fds \<Lambda>) s = - \<zeta>\<Zprime> s / \<zeta> s"
      by (intro eval_fds_mangoldt) (use that in auto)
    thus ?case unfolding logderiv_def by (auto simp add: field_simps)
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>. 1 < b x \<longrightarrow>
      ~\<integral> (P\<^sub>2 x) (\<lambda>s. eval_fds (fds \<Lambda>) s * x ᣔ s / s)
    = ~\<integral> (P\<^sub>2 x) (\<lambda>s. - (x ᣔ s / s * L\<zeta>\<Zprime> s))"
    using Hb by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in +\<infinity>.
    ║\<psi> x - 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (\<lambda>s. - (x ᣔ s / s * L\<zeta>\<Zprime> s))║ \<le> R x"
    using Hb by eventually_elim auto
  thus ?thesis unfolding f_def
    by eventually_elim (auto simp add: contour_integral_neg)
qed

lemma estimation_perron_psi:
  "(\<lambda>x. ║\<psi> x + 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║) \<in> rem_est (c / 4) 1"
proof -
  have "(\<lambda>x. ║\<psi> x + 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║) \<in> O(R)"
    by (intro eventually_le_imp_bigo' perron_psi)
  moreover have "R \<in> rem_est (c / 4) 1" by (rule estimation_R)
  ultimately show ?thesis unfolding rem_est_def by (rule landau_o.big_trans)
qed

theorem prime_number_theorem:
  "PNT_3 (c / 4) 1"
proof -
  define r where "r x \<equiv>
      ║\<psi> x + 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║
    + ║1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x) + x║" for x
  have "║\<psi> x - x║ \<le> r x" for x
  proof -
    have "║\<psi> x - x║ = ║(\<psi> x :: \<complex>) - x║"
      by (fold dist_complex_def, simp add: dist_real_def)
    also have "\<dots> \<le> ║\<psi> x - - 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║
      + ║x - - 1 / (2 * \<pi> * \<i>) * ~\<integral> (P\<^sub>2 x) (f x)║"
      by (fold dist_complex_def, rule dist_triangle2)
    finally show ?thesis unfolding r_def by (simp add: add_ac)
  qed
  hence "(\<lambda>x. \<psi> x - x) \<in> O(r)" by (rule le_imp_bigo)
  moreover have "r \<in> rem_est (c / 4) 1"
    unfolding r_def rem_est_def
    by (intro sum_in_bigo, fold rem_est_def)
       (rule estimation_perron_psi, rule estimation_P\<^sub>2)
  ultimately show ?thesis
    unfolding PNT_3_def rem_est_def by (rule landau_o.big_trans)
qed
end

no_notation pi ("\<pi>")
unbundle "prime_counting_notation"

lemma prime_numbert_theorem:
  shows "\<exists>c. (\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (-c * \<surd> (ln x)))"
proof
  define c where "c \<equiv> \<surd> (3 * C\<^sub>4 / 2) / 4"
  interpret z: prime_number_theorem "\<surd> (3 * C\<^sub>4 / 2)"
    by standard (use C\<^sub>4_gt_zero in auto)
  have "PNT_3 c 1" unfolding c_def by (rule z.prime_number_theorem)
  hence "PNT_1 c 1" by (auto intro: PNT_3_imp_PNT_1)
  thus "(\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (- c * \<surd> (ln x)))"
    unfolding PNT_1_def rem_est_def
    by (rule landau_o.big.ev_eq_trans1)
       (auto intro: eventually_at_top_linorderI [of 1] simp add: powr_half_sqrt)
qed
end
