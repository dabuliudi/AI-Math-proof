"""新编写的整除见证组合脚本；不调用现成Wronskian整除定理。"""
BODY = '''
theorem mathlib2_dvd_linear_combination {R : Type*} [Ring R]
    {q x y : R} (hx : q ∣ x) (hy : q ∣ y) (r s : R) :
    q ∣ x * r - y * s := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  refine ⟨u * r - v * s, ?_⟩
  rw [mul_sub, mul_assoc, mul_assoc]

theorem mathlib2_quotient_dvd_self {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) : a / radical a ∣ a := by
  simpa only [divRadical] using (divRadical_dvd_self a)

theorem mathlib2_mason_lemma2 {k : Type*} [Field k] [DecidableEq k]
    (a b : k[X]) (ha : a ≠ 0) : a / radical a ∣ wronskian a b := by
  change a / radical a ∣ a * derivative b - derivative a * b
  exact mathlib2_dvd_linear_combination
    (mathlib2_quotient_dvd_self a) (mathlib2_mason_lemma1 a ha)
    (derivative b) b

#print axioms mathlib2_dvd_linear_combination
#print axioms mathlib2_quotient_dvd_self
#print axioms mathlib2_mason_lemma2
#print mathlib2_mason_lemma2
'''


def template(lemma1_source):
    return dict(label='Mason–Stothers Lemma 2：新编写的组合证明',source=lemma1_source+BODY,
        target='∀ {k : Type*} [Field k] [DecidableEq k] (a b : k[X]), a ≠ 0 → a / radical a ∣ Polynomial.wronskian a b',
        name='mathlib2_mason_lemma2',scope='target',
        source_match=r'(?is)\bLemma\s*2\b.*?nonzero.*?rad\s*\(\s*a\s*\).*?divides\s*W',
        provenance={'category':'New Proof','new_statement':True,'new_proof':True,
            'meaning':'新编写的Lean组合证明，不主张新数学结果或全球独创；依赖已复用的Lemma1',
            'method':'提取两个整除见证u,v，构造u*derivative b-v*b，使用分配律和结合律',
            'author_code_copied':False,'ai_api_calls':0,'alternative_not_used':'divRadical_dvd_wronskian_left'},
        audit_names=['mathlib2_mason_lemma1','mathlib2_dvd_linear_combination','mathlib2_quotient_dvd_self','mathlib2_mason_lemma2'],
        reused_declarations=[{'name':'divRadical_dvd_derivative','path':'Mathlib/RingTheory/Polynomial/Radical.lean','line':31},
            {'name':'EuclideanDomain.divRadical_dvd_self','path':'Mathlib/RingTheory/Radical.lean','line':426}])
