# 按读回域陈述的充分性: 域, 结点出口的两侧, 链一支改成按关系支配

> 判决: 接口与编译定理, 无前提; 只导入标准库, `YiAbs*`, `YiFIIface`, `YiBLIface`, `YiBLToy`, 不读记号. 每个系统带一个树的域 `Dom` (沿第一位置序向下, 对后继, 结点分支, 嵌入左项封闭); 保持只对域里的树陈述 (`SuffD.keepAllᴰ`, `SuffRD.keepAllᴰ`, `sys→lowᴰ`, `SuffRAD`). 结点出口 `NodeOut` 只对域里的结点要, 走链一支的最后一项从 `⊴` 改成 "链点的像满足的关系, 结点的像也满足" (`⊴` 推出它: `out→outD`, `outR→outRD`).
> 结点出口拆成树一侧 `NodeTree` (每个域内结点: 有保留证据, 或给出链与它的支配; 槽位换型下关系的搬运) 与参照一侧 `NodeRef`, `assemble` 合成 `NodeOut`.
> 前提可满足: `YiBLToy` 的模型取全体为域, 经两条旧出口到新出口的换算得到 `toy-lowᴰ`. 不给出什么: 不构造域与关系. 实例在 [YiQDFold](YiQDFold.lagda.md), 链一支原形状的否定在 [YiQDNeg](YiQDNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQDIface where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGRow
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiBLToy using (module Toy)

module QD {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open Row 𝔾 𝔻
  open FI 𝔾 𝔻
  open BL 𝔾 𝔻
```

## 域与结点出口

域对生成规则里出现在前提中的同层树封闭: 放宽 (`dw`), 后继, 结点的每个分支, 嵌入的左项. 嵌入的孩子树不在本层, 它的封闭按行另给 (`dch`, `RowD`).

```agda
  module _ {j : Lv} (𝒮 : Sys j) where
    private module S = Sys 𝒮

    record Dom : Set₁ where
      field
        D   : ∀ {a} → S.St a → Tr a → Set
        dw  : ∀ {a} (s : S.St a) {x x′ : Tr a} → x ◃ x′ → D s x′ → D s x
        dsc : ∀ {a} (s : S.St a) {x : Tr a} → D s (sc x) → D s x
        dnd : ∀ {a} (s : S.St a) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → ∀ c → D s (g c)
        dup : ∀ {a} (s : S.St a) (x : Tr a) (c : Ch a) (y : ChT a c) → D s (up x c y) → D s x

    Chain : ∀ {a} (s : S.St a) (p : Sl a) (g : SlT a p → Tr a) → Set
    Chain {a} s p g = Σ (ℕ → SlT a p) λ z → ∀ k {τ} → R j τ (S.Φ s (g (z k))) → R j τ (S.Φ s (nd p g))

    NodeRes : S.KeepLaw → ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) (t κ : T) → Set
    NodeRes 𝓀 {a} s K p g t κ =
        (Σ (S.Ev s p) λ e → CΩ (S.ap K t) κ × (∀ η → fsT (S.ap K t) η ≡ S.ap K (fsT t η))
           × Nu j (slot s p e) κ
           × (∀ η c → R (slL j (slot s p e)) η (slT j (slot s p e) c) → R (slL a p) η (slT a p (mvc s p e c))))
      ⊎ (Σ (ℕ → T) λ γ → Σ (ℕ → SlT a p) λ z → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
           × (∀ k → R (slL a p) (γ k) (slT a p (z k))) × (∀ k {τ} → R j τ (S.Φ s (g (z k))) → R j τ (S.Φ s (nd p g))))
      where open S.KeepLaw 𝓀

    NodeOut : S.KeepLaw → (∀ {a} → S.St a → Tr a → Set) → Set
    NodeOut 𝓀 D = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) → D s (nd p g)
      → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
      → NodeRes 𝓀 s K p g t κ
```

树一侧: 域内结点二选一 (`pick`), 保留时槽位换型下关系照搬 (`mvR`). 参照一侧按 `pick` 的结果给剩下的项: 保留时三项, 走链时参照链 γ 与它对着链点.

```agda
    record NodeTree (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) : Set where
      open S.KeepLaw 𝓀
      field
        pick : ∀ {a} (s : S.St a) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → S.Ev s p ⊎ Chain s p g
        mvR  : ∀ {a} (s : S.St a) (p : Sl a) (e : S.Ev s p) → ∀ η c
             → R (slL j (slot s p e)) η (slT j (slot s p e) c) → R (slL a p) η (slT a p (mvc s p e c))

    NodeRefAt : S.KeepLaw → ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) (t κ : T)
      → S.Ev s p ⊎ Chain s p g → Set
    NodeRefAt 𝓀 s K p g t κ (inj₁ e) =
      CΩ (S.ap K t) κ × (∀ η → fsT (S.ap K t) η ≡ S.ap K (fsT t η)) × Nu j (S.KeepLaw.slot 𝓀 s p e) κ
    NodeRefAt 𝓀 {a} s K p g t κ (inj₂ (z , _)) =
      Σ (ℕ → T) λ γ → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k))) × (∀ k → R (slL a p) (γ k) (slT a p (z k)))

    NodeRef : (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) → NodeTree 𝓀 D → Set
    NodeRef 𝓀 D nt = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) (d : D s (nd p g))
      → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
      → NodeRefAt 𝓀 s K p g t κ (NodeTree.pick nt s p g d)

    assemble : (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) (nt : NodeTree 𝓀 D) → NodeRef 𝓀 D nt → NodeOut 𝓀 D
    assemble 𝓀 D nt rf {a} s K bd p {t} {κ} g d e nu hR = asm (NodeTree.pick nt s p g d) (rf s K bd p g d e nu hR)
      where
      asm : (r : S.Ev s p ⊎ Chain s p g) → NodeRefAt 𝓀 s K p g t κ r → NodeRes 𝓀 s K p g t κ
      asm (inj₁ ev)       (cΩ , fs , nu′)   = inj₁ (ev , cΩ , fs , nu′ , NodeTree.mvR nt s p ev)
      asm (inj₂ (z , dm)) (γ , cω , fs , ch) = inj₂ (γ , z , cω , fs , ch , dm)
```

## 回退系统的出口与充分性

`OutD` 与 `Out` 只差结点一条 (`NodeOut`). 结点一行的证明两种系统共用 (`nodeᴰ`).

```agda
    record OutD (Le : T → T → Set) (𝓀 : S.KeepLaw) (𝒻 : S.FallLaw) (D : ∀ {a} → S.St a → Tr a → Set) : Set where
      open S.FallLaw 𝒻
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        upE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → (c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
              → Σ S.Cxt λ K′ → S.Bdˢ (step s c x) K′ × (∀ u → S.ap K′ u ≡ S.ap K (t ⊕ u))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
        nodeE : NodeOut 𝓀 D

    nodeᴰ : (wk : Weak) (lm : Lim) (nod : Node) (𝓀 : S.KeepLaw) (𝒟 : Dom) → NodeOut 𝓀 (Dom.D 𝒟)
      → ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) {t κ : T} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ
      → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
      → (∀ η c → R (slL a p) η (slT a p c) → Dom.D 𝒟 s (g c) → S.Q s K (fsT t η) (g c))
      → Dom.D 𝒟 s (nd p g) → S.Q s K t (nd p g)
    nodeᴰ wk lm nod 𝓀 𝒟 nE s K bd p g e nu hR hQ d with nE s K bd p g d e nu hR
    ... | inj₁ (ev , cΩ , fs , nu′ , tr) = wk⊴ wk
          (nod (slot s p ev) (λ c → S.Φ s (g (mvc s p ev c))) cΩ nu′
            (λ η c l → subst (λ o → R j o (S.Φ s (g (mvc s p ev c)))) (sym (fs η))
              (hQ η (mvc s p ev c) (tr η c l) (Dom.dnd 𝒟 s p g d (mvc s p ev c)))))
          (keep s p ev g)
      where open S.KeepLaw 𝓀
    ... | inj₂ (γ , z , cω , fs , ch , dm) =
          lm cω (λ k → subst (λ o → R j o (S.Φ s (nd p g))) (sym (fs k)) (dm k (hQ (γ k) (z k) (ch k) (Dom.dnd 𝒟 s p g d (z k)))))

    module SuffD (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : S.Monoˢ)
                 (𝓀 : S.KeepLaw) (𝒻 : S.FallLaw) (𝒟 : Dom)
                 (dch : ∀ {a} (s : S.St a) c x y → Dom.D 𝒟 s (up x c y) → Dom.D 𝒟 (S.FallLaw.step 𝒻 s c x) (chT a c y))
                 (ex : OutD Le 𝓀 𝒻 (Dom.D 𝒟)) (gen : ∀ a → Gen⁺ Le a) where
      open S.FallLaw 𝒻
      open Dom 𝒟
      open OutD ex

      Qᴰ : ∀ {a} → S.St a → S.Cxt → T → Tr a → Set
      Qᴰ s K t x = D s x → S.Q s K t x

      rules : ∀ {a} → (∀ c (s′ : S.St (chL a c)) K′ → S.Bdˢ s′ K′ → ∀ {t x} → R (chL a c) t x → Qᴰ s′ K′ t x)
            → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → Rules a (Qᴰ s K)
      rules {a} child s K bd = record
        { qz = λ e _ → zeroE s K bd e
        ; q1 = λ e r q d → succE s K bd e r (q (dsc s d))
        ; qL = λ {t} {x} e _ h d → lm (proj₁ (limE s K bd e))
                 (λ n → subst (λ u → R j u (S.Φ s x)) (sym (proj₂ (limE s K bd e) n)) (h n d))
        ; qΩ = λ p g e nu hR hQ → nodeᴰ wk lm nod 𝓀 𝒟 nodeE s K bd p g e nu hR hQ
        ; qU = emb
        ; qw = λ _ q dd d → wk (q (dw s dd d)) (mono s dd) }
        where
        emb : (c : Ch a) {t u : T} {x : Tr a} (y : ChT a c) → R a t x → Qᴰ s K t x → R (chL a c) u (chT a c y)
            → Qᴰ s K (t ⊕ u) (up x c y)
        emb c {t} {u} {x} y r q ry d with upE s K bd c r (q (dup s x c y d))
        ... | K′ , bd′ , eq = wk⊴ wk
          (subst (λ o → R j o (S.Φ (step s c x) (chT a c y))) (eq u) (child c (step s c x) K′ bd′ ry (dch s c x y d)))
          (fall s c x y)

      keepAllᴰ : ∀ {a} → WfL a → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → ∀ {t x} → R a t x → D s x → S.Q s K t x
      keepAllᴰ {a} (wf f) s K bd =
        gen a (Qᴰ s K) (rules (λ c s′ K′ bd′ → keepAllᴰ (f c) s′ K′ bd′) s K bd) (λ le _ q d → leE s K bd le (q d))
```


旧出口给出新出口 (对任何域): `⊴` 经放宽推出按关系支配.

```agda
    OldRes NewRes : ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) (t : T) → Set
    OldRes {a} s K p g t = Σ (ℕ → T) λ γ → Σ (ℕ → SlT a p) λ z → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
      × (∀ k → R (slL a p) (γ k) (slT a p (z k))) × (∀ k → S.Φ s (g (z k)) ⊴ S.Φ s (nd p g))
    NewRes {a} s K p g t = Σ (ℕ → T) λ γ → Σ (ℕ → SlT a p) λ z → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
      × (∀ k → R (slL a p) (γ k) (slT a p (z k))) × (∀ k {τ} → R j τ (S.Φ s (g (z k))) → R j τ (S.Φ s (nd p g)))

    fromOld : (wk : Weak) {X : Set} → ∀ {a} {s : S.St a} {K p g t} → X ⊎ OldRes s K p g t → X ⊎ NewRes s K p g t
    fromOld wk (inj₁ x) = inj₁ x
    fromOld wk (inj₂ (γ , z , cω , fs , ch , tr)) = inj₂ (γ , z , cω , fs , ch , λ k r → wk⊴ wk r (tr k))

    out→outD : ∀ {Le 𝓀 𝒻} (wk : Weak) (D : ∀ {a} → S.St a → Tr a → Set) → S.Out Le 𝓀 𝒻 → OutD Le 𝓀 𝒻 D
    out→outD wk D ex = record
      { zeroE = S.Out.zeroE ex ; succE = S.Out.succE ex ; limE = S.Out.limE ex ; upE = S.Out.upE ex ; leE = S.Out.leE ex
      ; nodeE = λ s K bd p g _ e nu hR → fromOld wk (S.Out.nodeE ex s K bd p g e nu hR) }
```

树一侧给定之后出口剩下的参照一侧 (`OutDT`): 五条与 `Out` 相同, 结点一条只剩 `NodeRef`.

```agda
    record OutDT (Le : T → T → Set) (𝓀 : S.KeepLaw) (𝒻 : S.FallLaw) (D : ∀ {a} → S.St a → Tr a → Set) (nt : NodeTree 𝓀 D) : Set where
      open S.FallLaw 𝒻
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        upE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → (c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
              → Σ S.Cxt λ K′ → S.Bdˢ (step s c x) K′ × (∀ u → S.ap K′ u ≡ S.ap K (t ⊕ u))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
        nodeR : NodeRef 𝓀 D nt

    outDT→outD : ∀ {Le 𝓀 𝒻} {D : ∀ {a} → S.St a → Tr a → Set} {nt} → OutDT Le 𝓀 𝒻 D nt → OutD Le 𝓀 𝒻 D
    outDT→outD {𝓀 = 𝓀} {D = D} {nt = nt} ex = record
      { zeroE = OutDT.zeroE ex ; succE = OutDT.succE ex ; limE = OutDT.limE ex ; upE = OutDT.upE ex ; leE = OutDT.leE ex
      ; nodeE = assemble 𝓀 D nt (OutDT.nodeR ex) }
```

## 换基系统的出口与充分性

行上的域条件: 回退行要求孩子树落在孩子状态的域里, 换基行要求替身落在辅助系统的域里. 换基行的 "替身支配原材料" 只对域里的嵌入要 (`EmbOutD`; 旧形状推出它, `embOut→D`).

```agda
  module _ {j : Lv} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) (ℯ : EmbLaw 𝒮 𝒜 𝓀ᴬ) where
    private
      module S = Sys 𝒮
      module A = Sys 𝒜
    open EmbLaw ℯ

    RowD : (D : ∀ {a} → S.St a → Tr a → Set) (Dᴬ : ∀ {a} → A.St a → Tr a → Set)
      → ∀ {a} (s : S.St a) → FallAt 𝒮 𝒜 𝓀ᴬ s ⊎ RebAt 𝒮 𝒜 𝓀ᴬ s → Set
    RowD D Dᴬ {a} s (inj₁ f) = ∀ c x y → D s (up x c y) → D (FallAt.step f c x) (chT a c y)
    RowD D Dᴬ {a} s (inj₂ r) = ∀ c x → Dᴬ (RebAt.Sr r c x) (RebAt.sub r c x)

    EmbOutD : (Le : T → T → Set) (D : ∀ {a} → S.St a → Tr a → Set)
      → ∀ {a} (s : S.St a) → S.Cxt → FallAt 𝒮 𝒜 𝓀ᴬ s ⊎ RebAt 𝒮 𝒜 𝓀ᴬ s → Set
    EmbOutD Le D s K (inj₁ f) = EmbOut 𝒮 𝒜 𝓀ᴬ ℯ Le s K (inj₁ f)
    EmbOutD Le D {a} s K (inj₂ r) =
        ((c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
          → Σ A.Cxt λ K″ → A.Bdˢ (RebAt.Sr r c x) K″ × (∀ u → A.ap K″ u ≡ S.ap K (t ⊕ u)))
      × ((c : Ch a) → ∀ {t u x} (y : ChT a c) → D s (up x c y) → R a t x → R (chL a c) u (chT a c y)
          → Σ T λ u″ → R (RebAt.Lr r c x) u″ (RebAt.sub r c x) × Le (t ⊕ u) (t ⊕ u″))

    embOut→D : ∀ {Le} {D : ∀ {a} → S.St a → Tr a → Set} {a} (s : S.St a) K (w : FallAt 𝒮 𝒜 𝓀ᴬ s ⊎ RebAt 𝒮 𝒜 𝓀ᴬ s)
      → EmbOut 𝒮 𝒜 𝓀ᴬ ℯ Le s K w → EmbOutD Le D s K w
    embOut→D s K (inj₁ f) E         = E
    embOut→D s K (inj₂ r) (E₁ , E₂) = E₁ , λ c y _ → E₂ c y

    record OutRD (Le : T → T → Set) (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) : Set where
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
        nodeE : NodeOut 𝒮 𝓀 D
        embE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → EmbOutD Le D s K (row s)

    outR→outRD : ∀ {Le 𝓀} (wk : Weak) (D : ∀ {a} → S.St a → Tr a → Set) → OutR 𝒮 𝒜 𝓀ᴬ ℯ Le 𝓀 → OutRD Le 𝓀 D
    outR→outRD wk D ex = record
      { zeroE = OutR.zeroE ex ; succE = OutR.succE ex ; limE = OutR.limE ex ; leE = OutR.leE ex
      ; nodeE = λ s K bd p g _ e nu hR → fromOld 𝒮 wk (OutR.nodeE ex s K bd p g e nu hR)
      ; embE = λ s K bd → embOut→D s K (row s) (OutR.embE ex s K bd) }

    record OutRDT (Le : T → T → Set) (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) (nt : NodeTree 𝒮 𝓀 D) : Set where
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
        nodeR : NodeRef 𝒮 𝓀 D nt
        embE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → EmbOutD Le D s K (row s)

    outRDT→outRD : ∀ {Le 𝓀} {D : ∀ {a} → S.St a → Tr a → Set} {nt} → OutRDT Le 𝓀 D nt → OutRD Le 𝓀 D
    outRDT→outRD {𝓀 = 𝓀} {D = D} {nt = nt} ex = record
      { zeroE = OutRDT.zeroE ex ; succE = OutRDT.succE ex ; limE = OutRDT.limE ex ; leE = OutRDT.leE ex
      ; nodeE = assemble 𝒮 𝓀 D nt (OutRDT.nodeR ex) ; embE = OutRDT.embE ex }
```

同 `SuffR`: 回退行用孩子层的结论, 换基行用辅助系统上按域的保持 `auxK`.

```agda
    module SuffRD (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : S.Monoˢ)
                  (𝓀 : S.KeepLaw) (𝒟 : Dom 𝒮) (Dᴬ : ∀ {a} → A.St a → Tr a → Set)
                  (rowD : ∀ {a} (s : S.St a) → RowD (Dom.D 𝒟) Dᴬ s (row s))
                  (ex : OutRD Le 𝓀 (Dom.D 𝒟))
                  (auxK : ∀ {b} (s′ : A.St b) K″ → A.Bdˢ s′ K″ → ∀ {u x} → R b u x → Dᴬ s′ x → A.Q s′ K″ u x)
                  (gen : ∀ a → Gen⁺ Le a) where
      open Dom 𝒟
      open OutRD ex

      Qᴰ : ∀ {a} → S.St a → S.Cxt → T → Tr a → Set
      Qᴰ s K t x = D s x → S.Q s K t x

      rules : ∀ {a} → (∀ c (s′ : S.St (chL a c)) K′ → S.Bdˢ s′ K′ → ∀ {t x} → R (chL a c) t x → Qᴰ s′ K′ t x)
            → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → Rules a (Qᴰ s K)
      rules {a} child s K bd = record
        { qz = λ e _ → zeroE s K bd e
        ; q1 = λ e r q d → succE s K bd e r (q (dsc s d))
        ; qL = λ {t} {x} e _ h d → lm (proj₁ (limE s K bd e))
                 (λ n → subst (λ u → R j u (S.Φ s x)) (sym (proj₂ (limE s K bd e) n)) (h n d))
        ; qΩ = λ p g e nu hR hQ → nodeᴰ 𝒮 wk lm nod 𝓀 𝒟 nodeE s K bd p g e nu hR hQ
        ; qU = emb
        ; qw = λ _ q dd d → wk (q (dw s dd d)) (mono s dd) }
        where
        emb : (c : Ch a) {t u : T} {x : Tr a} (y : ChT a c) → R a t x → Qᴰ s K t x → R (chL a c) u (chT a c y)
            → Qᴰ s K (t ⊕ u) (up x c y)
        emb c {t} {u} {x} y r q ry d with row s | embE s K bd | rowD s
        ... | inj₁ f | E | rd with E c r (q (dup s x c y d))
        ...   | K′ , bd′ , eq = wk⊴ wk
          (subst (λ o → R j o (S.Φ (FallAt.step f c x) (chT a c y))) (eq u)
            (child c (FallAt.step f c x) K′ bd′ ry (rd c x y d)))
          (FallAt.fall f c x y)
        emb c {t} {u} {x} y r q ry d | inj₂ rw | (E₁ , E₂) | rd with E₁ c r (q (dup s x c y d)) | E₂ c y d r ry
        ...   | K″ , bd″ , eq | u″ , rs , le = leE s K bd le
          (subst (λ o → R j o (S.Φ s (up x c y))) (eq u″)
            (wk⊴ wk (auxK (RebAt.Sr rw c x) K″ bd″ rs (rd c x)) (RebAt.reb rw c x y)))

      keepAllᴰ : ∀ {a} → WfL a → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → ∀ {t x} → R a t x → D s x → S.Q s K t x
      keepAllᴰ {a} (wf f) s K bd =
        gen a (Qᴰ s K) (rules (λ c s′ K′ bd′ → keepAllᴰ (f c) s′ K′ bd′) s K bd) (λ le _ q d → leE s K bd le (q d))

      sys→lowᴰ : ∀ {ℓ} → WfL ℓ → (s : S.St ℓ) (K : S.Cxt) → S.Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j)
        → (∀ x → S.Φ s x ≡ ψ ℓ b j w β x) → (∀ t → S.ap K t ≡ app Kc t)
        → ∀ {a x} → D s x → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)
      sys→lowᴰ W s K bd b w β Kc eΦ ec {a} {x} d r =
        subst (λ o → R j (app Kc a) o) (eΦ x) (subst (λ u → R j u (S.Φ s x)) (ec a) (keepAllᴰ W s K bd r d))
```

辅助系统按自己的域满足 `OutD`, 各层良基, 则 `auxK` 由 `SuffD.keepAllᴰ` 给出.

```agda
    module SuffRAD (Le : T → T → Set) (wk : Weak) (lm : Lim) (nod : Node) (mono : S.Monoˢ)
                   (𝓀 : S.KeepLaw) (𝒟 : Dom 𝒮) (𝒟ᴬ : Dom 𝒜)
                   (rowD : ∀ {a} (s : S.St a) → RowD (Dom.D 𝒟) (Dom.D 𝒟ᴬ) s (row s))
                   (ex : OutRD Le 𝓀 (Dom.D 𝒟))
                   (monoᴬ : A.Monoˢ) (𝒻ᴬ : A.FallLaw)
                   (dchᴬ : ∀ {a} (s : A.St a) c x y → Dom.D 𝒟ᴬ s (up x c y) → Dom.D 𝒟ᴬ (A.FallLaw.step 𝒻ᴬ s c x) (chT a c y))
                   (exᴬ : OutD 𝒜 Le 𝓀ᴬ 𝒻ᴬ (Dom.D 𝒟ᴬ)) (wfAll : ∀ b → WfL b)
                   (gen : ∀ a → Gen⁺ Le a) where
      private module SA = SuffD 𝒜 Le wk lm nod monoᴬ 𝓀ᴬ 𝒻ᴬ 𝒟ᴬ dchᴬ exᴬ gen
      open SuffRD Le wk lm nod mono 𝓀 𝒟 (Dom.D 𝒟ᴬ) rowD ex (λ {b} s′ → SA.keepAllᴰ (wfAll b) s′) gen public
```

## 模型: 前提可满足

`YiBLToy` 的两层模型, 域取全体, 出口由旧出口换算.

```agda
module ToyD (𝕍 : Val) where
  open import Data.Nat using (_≤_; _+_)
  open import Data.Bool using (true; false)
  open import Data.Unit using (⊤; tt)
  open Toy 𝕍
  open QD graded doms

  dom⊤ : Dom sys
  dom⊤ = record { D = λ _ _ → ⊤ ; dw = λ _ _ _ → tt ; dsc = λ _ _ → tt ; dnd = λ _ _ _ _ _ → tt ; dup = λ _ _ _ _ _ → tt }

  rowD⊤ : ∀ {a} (β : ℕ) → RowD sys sys keepᵗ embᵗ (λ _ _ → ⊤) (λ _ _ → ⊤) {a} β (rowᵗ β)
  rowD⊤ {a = true}  β = λ _ _ → tt
  rowD⊤ {a = false} β = λ _ _ _ _ → tt

  toy-lowᴰ : (β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x
  toy-lowᴰ β K bd r = SuffRAD.sys→lowᴰ sys sys keepᵗ embᵗ _≤_ weakᵗ limᵗ nodeᵗ monoᵗ keepᵗ dom⊤ dom⊤ rowD⊤
    (outR→outRD sys sys keepᵗ embᵗ weakᵗ (λ _ _ → ⊤) outRᵗ) monoᵗ fallᵗ (λ _ _ _ _ _ → tt)
    (out→outD sys weakᵗ (λ _ _ → ⊤) outᵗ) wfᵗ genᵗ (wfᵗ true) β K bd tt tt β K (λ _ → refl) (λ _ → refl) tt r
```
