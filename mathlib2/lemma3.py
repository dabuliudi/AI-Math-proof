"""本次助手新编写的证明候选，随后固化供复跑；不是自动推理引擎。"""
SOURCE = '''import Mathlib.RingTheory.Polynomial.Radical
open Polynomial UniqueFactorizationMonoid EuclideanDomain

theorem mathlib2_unit_of_natDegree_zero {k : Type*} [Field k]
    (a : k[X]) (ha : a ≠ 0) (hz : a.natDegree = 0) : IsUnit a := by
  apply isUnit_iff_degree_eq_zero.mpr
  rw [degree_eq_natDegree ha, hz]
  rfl

theorem mathlib2_unit_of_radical_unit {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (ha : a ≠ 0) (hu : IsUnit (radical a)) : IsUnit a := by
  have hr : radical a = 1 := by
    calc
      radical a = radical (radical a) := radical_radical.symm
      _ = 1 := radical_of_isUnit hu
  exact (radical_eq_one_iff.mp hr).resolve_left ha

theorem mathlib2_radical_natDegree_ne_zero {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : 1 ≤ a.natDegree) : (radical a).natDegree ≠ 0 := by
  have hn : a.natDegree ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one h)
  have ha : a ≠ 0 := fun hz => hn (by simp [hz])
  intro hz
  have hu := mathlib2_unit_of_natDegree_zero (radical a) radical_ne_zero hz
  have hau := mathlib2_unit_of_radical_unit a ha hu
  exact hn (natDegree_eq_zero_of_isUnit hau)

theorem mathlib2_mason_lemma3_nat {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : 1 ≤ a.natDegree) : 1 ≤ (radical a).natDegree := by
  exact Nat.one_le_iff_ne_zero.mpr (mathlib2_radical_natDegree_ne_zero a h)

theorem mathlib2_mason_lemma3 {k : Type*} [Field k] [DecidableEq k]
    (a : k[X]) (h : (1 : WithBot ℕ) ≤ a.degree) :
    (1 : WithBot ℕ) ≤ (radical a).degree := by
  have hnat : 1 ≤ a.natDegree := Nat.succ_le_of_lt
    (natDegree_pos_iff_degree_pos.mpr (lt_of_lt_of_le (by decide) h))
  rw [degree_eq_natDegree radical_ne_zero]
  exact WithBot.coe_le_coe.mpr (mathlib2_mason_lemma3_nat a hnat)

#print axioms mathlib2_unit_of_natDegree_zero
#print axioms mathlib2_unit_of_radical_unit
#print axioms mathlib2_radical_natDegree_ne_zero
#print axioms mathlib2_mason_lemma3_nat
#print axioms mathlib2_mason_lemma3
#print mathlib2_mason_lemma3
'''

REFS = [
    ('Polynomial.isUnit_iff_degree_eq_zero','Algebra/Polynomial/FieldDivision.lean',286),
    ('Polynomial.degree_eq_natDegree','Algebra/Polynomial/Degree/Definitions.lean',93),
    ('UniqueFactorizationMonoid.radical_radical','RingTheory/Radical.lean',268),
    ('UniqueFactorizationMonoid.radical_of_isUnit','RingTheory/Radical.lean',180),
    ('UniqueFactorizationMonoid.radical_eq_one_iff','RingTheory/Radical.lean',259),
    ('UniqueFactorizationMonoid.radical_ne_zero','RingTheory/Radical.lean',212),
    ('Polynomial.natDegree_eq_zero_of_isUnit','Algebra/Polynomial/Degree/Units.lean',27),
    ('Polynomial.natDegree_pos_iff_degree_pos','Algebra/Polynomial/Degree/Definitions.lean',511),
    ('WithBot.coe_le_coe','Order/WithBot.lean',245),
]

def template():
    names=['mathlib2_unit_of_natDegree_zero','mathlib2_unit_of_radical_unit',
        'mathlib2_radical_natDegree_ne_zero','mathlib2_mason_lemma3_nat','mathlib2_mason_lemma3']
    return dict(label='Mason–Stothers Lemma 3：次数与 radical',source=SOURCE,
        target='∀ {k : Type*} [Field k] [DecidableEq k] (a : k[X]), (1 : WithBot ℕ) ≤ a.degree → (1 : WithBot ℕ) ≤ (radical a).degree',
        name=names[-1],scope='target',source_match=r'(?is)\bLemma\s*3\b.*?field.*?degree.*?rad',
        audit_names=names,reused_declarations=[{'name':n,'path':'Mathlib/'+p,'line':l} for n,p,l in REFS],
        provenance={'category':'New Proof','new_proof':True,'new_statement':True,
            'generation_source':'AI 生成（本次对话助手编写代码）；随后固化为复跑模板',
            'autonomous_reasoning_engine':False,'external_ai_api_calls':0,'author_code_copied':False,
            'meaning':'新的Lean组合脚本，不主张新数学结果；未复制作者实现',
            'lemma1_used':False,'lemma2_used':False})
