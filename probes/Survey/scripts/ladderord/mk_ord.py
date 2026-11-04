# 由 LadderInf* 生成对结构 HtB 参数化的 LadderOrd*: 换名字, 只有 Omega 有手写补丁 (链行的单调不再靠 view-step).
# 用法: python3 mk_ord.py [模块名...]
import re,os,sys
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
MODS='Tree Rel Cx Rules Rules2 Rules3 Strict Strict2 Strict3 Class ClassF Good Vis Read Iota Tr Add Psi PsiH Eval Tail Mono Root Omega Main Dn DnSelf'.split()

OLD_STEP='''step-mono : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → view n′ ≡ clos r → stepL (tr< r q′) (Ω̇ n) ⊑ᵗ stepL q′ (Ω̇ n′)
step-mono {n} {n′} {m} r q′ e =
  wk-lᵗ (wk-rᵗ (⊑ᵀ→ᵗ (R-ι↓ (tr< r q′) z≅ (RΩ̇ n z≅))
    (⊑ᵀ-Rˡʷ (λ u → u) (upd-sub n′ (λ i q u → κ-cap n (λ _ → tt) i u) (λ u → u)) (R-ιι↓ r q′ z≅ (RΩ̇ n z≅)) (ιD-cong {qd = q′} (ι↓⊑row r e)))))
'''
NEW_STEP='''-- 这里是与 LadderInfOmega 唯一的不同. 原文件靠 view-step: 链的下一项是上一项的闭包, 在 ω² 上是假的.
-- 改成对高度归纳: 一切 n < m 都有 ι↓ (Ω̇ n 0) ⊑ Ω̇ m 0. 闭包行与链行各用 view-ok 把 n 压到写法给的那个高度以下.
comp↓ : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ n′ zero → ι↓ {α = zero} (tr< r q′) (Ω̇ n zero) ⊑ᵀ ι↓ {α = zero} q′ (Ω̇ n′ zero)
comp↓ {n} {n′} r q′ h = ⊑ᵀ-Rˡʷ (λ u → u) (upd-sub n′ (λ i q u → κ-cap n (λ _ → tt) i u) (λ u → u)) (R-ιι↓ r q′ z≅ (RΩ̇ n z≅)) (ιD-cong {qd = q′} h)

XM : Ht → Set
XM m = ∀ {n} (r : n <ᴸ m) → ι↓ {α = zero} r (Ω̇ n zero) ⊑ᵀ Ω̇ m zero

ι↓⊑chain : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → view m ≡ chain F qs₁ → ∀ i → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ Ω̇ m zero
ι↓⊑chain {m} F qs₁ e i = subst (λ X → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ X) (sym (cong (rowV m (ΩI m)) e))
  (lim-rᵀ (suc i) (subst (λ X → ι↓ {α = zero} (qs₁ i) (Ω̇ (F i) zero) ⊑ᵀ stepL (qs₁ i) X) (sym (ΩI≡ (qs₁ i))) (wk-rᵀ (R→⊑ᵀ (R-ι↓ (qs₁ i) z≅ (RΩ̇ (F i) z≅))))))

low-row : ∀ m → (∀ {n} → n <ᴸ m → XM n) → (v : View _<ᴸ_ h₀ m) → ViewOk _<ᴸ_ h₀ m v → view m ≡ v → XM m
low-row _ I base ok e r = ⊥-elim (no< r)
low-row m I (clos {n = n′} q) ok e {n} r with ok r
... | inj₁ refl = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop q r) (ι↓⊑row q e)
... | inj₂ r₁ = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (tr< r₁ q) r)
  (⊑ᵀ-transʷ (λ u → u) (⇑ (κ-cap n′ (λ _ → tt))) (comp↓ r₁ q (I q r₁)) (ι↓⊑row q e))
low-row m I (chain F qs₁) (asc , cof) e {n} r with cof r
... | i , inj₁ refl = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (qs₁ i) r) (ι↓⊑chain F qs₁ e i)
... | i , inj₂ r₁ = subst (λ r₀ → ι↓ {α = zero} r₀ (Ω̇ n zero) ⊑ᵀ Ω̇ m zero) (<-prop (tr< r₁ (qs₁ i)) r)
  (⊑ᵀ-transʷ (λ u → u) (⇑ (κ-cap (F i) (λ _ → tt))) (comp↓ r₁ (qs₁ i) (I (qs₁ i) r₁)) (ι↓⊑chain F qs₁ e i))

FM : ∀ m → (∀ {n} → n <ᴸ m → XM n) → XM m
FM m I = low-row m I (view m) (view-ok m) refl

low⊑ : ∀ m → XM m
low⊑ m = FM m (Rec XM FM m)

step-mono : ∀ {n n′ m} (r : n <ᴸ n′) (q′ : n′ <ᴸ m) → stepL (tr< r q′) (Ω̇ n) ⊑ᵗ stepL q′ (Ω̇ n′)
step-mono {n} {n′} {m} r q′ =
  wk-lᵗ (wk-rᵗ (⊑ᵀ→ᵗ (R-ι↓ (tr< r q′) z≅ (RΩ̇ n z≅)) (comp↓ r q′ (low⊑ n′ r))))
'''
OLD_MONO='''mono-rowL : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → view m ≡ chain F qs₁ → ∀ i → rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i ⊑ᵗ rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) (suc i)
mono-rowL {m} F qs₁ ev zero = subst (λ X → 𝟏L {m} ⊑ᵗ stepL (qs₁ 0) X) (sym (ΩI≡ (qs₁ 0)))
  (⊑ᵀ→ᵗ R-𝟏L (wk-lᵀ (wk-rᵀ (𝟏-D {qd = qs₁ 0} (𝟏⊑Ω̇ (F 0) zero)))))
mono-rowL {m} F qs₁ ev (suc i) with view-step ev i
... | r , vw , qe = subst₂ (λ X Y → stepL (qs₁ i) X ⊑ᵗ stepL (qs₁ (suc i)) Y) (sym (ΩI≡ (qs₁ i))) (sym (ΩI≡ (qs₁ (suc i))))
  (subst (λ q₀ → stepL q₀ (Ω̇ (F i)) ⊑ᵗ stepL (qs₁ (suc i)) (Ω̇ (F (suc i)))) (sym qe) (step-mono r (qs₁ (suc i)) vw))
'''
NEW_MONO='''mono-rowL : ∀ {m} F (qs₁ : ∀ i → F i <ᴸ m) → (∀ i → F i <ᴸ F (suc i)) → ∀ i → rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) i ⊑ᵗ rowL F qs₁ (λ i₁ → ΩI m (qs₁ i₁)) (suc i)
mono-rowL {m} F qs₁ asc zero = subst (λ X → 𝟏L {m} ⊑ᵗ stepL (qs₁ 0) X) (sym (ΩI≡ (qs₁ 0)))
  (⊑ᵀ→ᵗ R-𝟏L (wk-lᵀ (wk-rᵀ (𝟏-D {qd = qs₁ 0} (𝟏⊑Ω̇ (F 0) zero)))))
mono-rowL {m} F qs₁ asc (suc i) = subst₂ (λ X Y → stepL (qs₁ i) X ⊑ᵗ stepL (qs₁ (suc i)) Y) (sym (ΩI≡ (qs₁ i))) (sym (ΩI≡ (qs₁ (suc i))))
  (subst (λ q₀ → stepL q₀ (Ω̇ (F i)) ⊑ᵗ stepL (qs₁ (suc i)) (Ω̇ (F (suc i)))) (<-prop (tr< (asc i) (qs₁ (suc i))) (qs₁ i)) (step-mono (asc i) (qs₁ (suc i))))
'''
OLD_ROWG='''rowG w m I (chain F qs₁) ev = Gmono (KQ→Ctx w) (gl (G-rowL w F qs₁ I) (mono-rowL F qs₁ ev))
'''
NEW_ROWG='''rowG w m I (chain F qs₁) ev = Gmono (KQ→Ctx w) (gl (G-rowL w F qs₁ I) (mono-rowL F qs₁ (proj₁ (subst (ViewOk _<ᴸ_ h₀ m) ev (view-ok m)))))
'''
PATCH={'Omega':[(OLD_STEP,NEW_STEP),(OLD_MONO,NEW_MONO),(OLD_ROWG,NEW_ROWG)]}
def clone(M):
    t=open(A+'LadderInf'+M+'.lagda.md',encoding='utf-8').read()
    title,rest=t.split('\n',1)
    title=title.replace('高度抽象','序数高度').replace('HtS','HtB')
    note='\n> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInf'+M+'](LadderInf'+M+'.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). '+('这一个模块有手写补丁: 链行的单调 (`low⊑`, `mono-rowL`). ' if M in PATCH else '除了名字逐字相同. ')+'下面的说明是原文件的.\n>'
    for a,b in PATCH.get(M,[]):
        if a not in rest:
            print('PATCH MISS',M,repr(a[:90]))
        else:
            rest=rest.replace(a,b)
    rest=rest.replace('LadderInf','LadderOrd').replace('HtS','HtB')
    # 说明里指回原文件的链接不要改名
    t=title+'\n'+note+rest
    open(A+'LadderOrd'+M+'.lagda.md','w',encoding='utf-8').write(t)
for M in (sys.argv[1:] or MODS):
    clone(M)
