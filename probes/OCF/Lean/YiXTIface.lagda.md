# 结点出口按保留判定的三个出口分解 (抽象)

> 判决: 接口与编译定理, 无前提; 只导入标准库, `YiAbs*`, `YiFIIface`, `YiBLIface`, `YiQDIface`, 不读记号. 每个槽位带一个出口 (`XPick`: 保留 `kept`, 同层或高于 `high`, 分叉 `cross`; 后两者无保留证据) 的系统, 树一侧 `NodeTree` 由出口给出 (`XTree.nt`).
> 参照一侧两条按字面层号的前提 (`Below`: 目标有同层真槽位就保留; `AboveL`: 无证据且目标到槽位层号有字面路径就沿树的链) 之下, 对 `nt` 的参照义务 `NodeRef` 当且仅当分叉一份 (`split`, `need`, `exact`), 合成结点出口 (`out`). 不管树一侧怎么选, 无证据而目标有同层真槽位的点上 `Below` 与 "余尾 ω 不是余尾 Ω" 推出结点出口不成立 (`stuck`, `out-stuck`). `OutDN`, `OutRDN`: 出口去掉结点一条.
> 不给出什么: 不涉及值; `Below`, `AboveL` 是参照接口的前提, 没有对记号实填. 具体折叠的实例在 [YiXTCur](YiXTCur.lagda.md), [YiXTReb](YiXTReb.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXTIface where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiBLIface
open import OCF.Lean.YiQDIface

module XT {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻
  open QD 𝔾 𝔻
```

## 出口与参照一侧的两条前提

`XPick s p`: 同 `YiCMExit.Exit` 的三种, 换成系统的证据. `RefKeepAt`, `RefChain` 是 `NodeRefAt` 两支的内容.

```agda
  module _ {j : Lv} (𝒮 : Sys j) where
    private module S = Sys 𝒮

    data XPick {a : Lv} (s : S.St a) (p : Sl a) : Set where
      kept  : S.Ev s p → XPick s p
      high  : (S.Ev s p → ⊥) → j ⊑ slL a p → XPick s p
      cross : (S.Ev s p → ⊥) → ∀ {k′} {h′ : Tr k′ → Lv} (c c′ : Tr k′) → slL a p ⊑ h′ c → j ⊑ h′ c′ → XPick s p

    RefKeepAt : ∀ {a} (s : S.St a) (K : S.Cxt) (q : Sl j) (t κ : T) → Set
    RefKeepAt s K q t κ = CΩ (S.ap K t) κ × (∀ η → fsT (S.ap K t) η ≡ S.ap K (fsT t η)) × Nu j q κ

    RefChain : ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) (t : T) → Chain 𝒮 s p g → Set
    RefChain {a} s K p g t (z , _) = Σ (ℕ → T) λ γ → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
      × (∀ k → R (slL a p) (γ k) (slT a p (z k)))
```

`Below` 只看字面层号 (目标的槽位 q 与槽位 p 同层), 不看树是否保留.

```agda
    Below : Set
    Below = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} → CΩ t κ → Nu a p κ
      → (q : Sl j) → slL j q ≡ slL a p → RefKeepAt s K q t κ
```

## 无证据处只能走链; 与 `Below` 冲突的点

对任何保留律 (任何树一侧): 没有保留证据时 `NodeRes` 只能是链一支, 参照上下文的余尾是 ω.

```agda
    noev→ω : ∀ {𝓀 : S.KeepLaw} {a} {s : S.St a} {K p g t κ} → NodeRes 𝒮 𝓀 s K p g t κ → (S.Ev s p → ⊥) → Cω (S.ap K t)
    noev→ω (inj₁ (ev , _)) ne = ⊥-elim (ne ev)
    noev→ω (inj₂ (_ , _ , cω , _)) ne = cω

    stuck : Below → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ {𝓀 : S.KeepLaw} {a} (s : S.St a) K → S.Bdˢ s K
      → (p : Sl a) {t : T} (g : SlT a p → Tr a) → CΩ t κ → Nu a p κ → (S.Ev s p → ⊥)
      → (q : Sl j) → slL j q ≡ slL a p → NodeRes 𝒮 𝓀 s K p g t κ → ⊥
    stuck bl dω {𝓀} s K bd p g e nu ne q lv r = dω (noev→ω {𝓀 = 𝓀} r ne) (proj₁ (bl s K bd p e nu q lv))

    out-stuck : Below → ∀ {κ} → (∀ {u} → Cω u → CΩ u κ → ⊥) → ∀ (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set)
      → NodeOut 𝒮 𝓀 D → ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) {t : T} (g : SlT a p → Tr a) → D s (nd p g)
      → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
      → (S.Ev s p → ⊥) → (q : Sl j) → slL j q ≡ slL a p → ⊥
    out-stuck bl dω 𝓀 D no s K bd p g d e nu hR ne q lv =
      stuck bl dω {𝓀 = 𝓀} s K bd p g e nu ne q lv (no s K bd p g d e nu hR)
```

## 由出口给出的树一侧

`XTree`: 每个槽位的出口 (`xp`), 无证据时树自己的链与它的支配 (`ch`), 保留时层号不变 (`lvl`) 与换型下关系照搬 (`mvR`). `nt`: 保留出口取证据, 另两个出口取链.

```agda
    module _ (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) where
      open S.KeepLaw 𝓀

      record XTree : Set where
        field
          xp  : ∀ {a} (s : S.St a) (p : Sl a) → XPick s p
          ch  : ∀ {a} (s : S.St a) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → (S.Ev s p → ⊥) → Chain 𝒮 s p g
          lvl : ∀ {a} (s : S.St a) (p : Sl a) (e : S.Ev s p) → slL j (slot s p e) ≡ slL a p
          mvR : ∀ {a} (s : S.St a) (p : Sl a) (e : S.Ev s p) → ∀ η c
              → R (slL j (slot s p e)) η (slT j (slot s p e) c) → R (slL a p) η (slT a p (mvc s p e c))

        forget : ∀ {a} (s : S.St a) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → XPick s p → S.Ev s p ⊎ Chain 𝒮 s p g
        forget s p g d (kept e)           = inj₁ e
        forget s p g d (high ne _)        = inj₂ (ch s p g d ne)
        forget s p g d (cross ne _ _ _ _) = inj₂ (ch s p g d ne)

        nt : NodeTree 𝒮 𝓀 D
        nt = record { pick = λ s p g d → forget s p g d (xp s p) ; mvR = mvR }
```

## 分解

`At P`: 在每个域内结点 (参照项余尾 Ω, 槽位允许 κ) 上, 按该槽位的出口取 P. `PartX`: 只在分叉出口上要参照沿树的链, 其余出口上为真. `AboveL` 按字面路径陈述, 不看出口.

```agda
      module _ (xt : XTree) where
        open XTree xt

        At : (∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → T → T → XPick s p → Set) → Set
        At P = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) (d : D s (nd p g))
          → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c)) → P s K p g d t κ (xp s p)

        PartX : ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → T → T → XPick s p → Set
        PartX s K p g d t κ (cross ne _ _ _ _) = RefChain s K p g t (ch s p g d ne)
        PartX s K p g d t κ (kept _)           = ⊤
        PartX s K p g d t κ (high _ _)         = ⊤

        AboveL : Set
        AboveL = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) (d : D s (nd p g))
          → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
          → (ne : S.Ev s p → ⊥) → j ⊑ slL a p → RefChain s K p g t (ch s p g d ne)
```

保留出口由 `Below` 与 `lvl` 给出, 同层或高于的出口由 `AboveL` 给出; 剩下的义务恰是分叉一份.

```agda
        split : Below → AboveL → At PartX → NodeRef 𝒮 𝓀 D nt
        split bl ab cx s K bd p {t} {κ} g d e nu hR = go (xp s p) (cx s K bd p g d e nu hR)
          where
          go : (x : XPick s p) → PartX s K p g d t κ x → NodeRefAt 𝒮 𝓀 s K p g t κ (forget s p g d x)
          go (kept ev)          _ = bl s K bd p e nu (slot s p ev) (lvl s p ev)
          go (high ne u)        _ = ab s K bd p g d e nu hR ne u
          go (cross ne _ _ _ _) r = r

        need : NodeRef 𝒮 𝓀 D nt → At PartX
        need nr s K bd p {t} {κ} g d e nu hR = go (xp s p) (nr s K bd p g d e nu hR)
          where
          go : (x : XPick s p) → NodeRefAt 𝒮 𝓀 s K p g t κ (forget s p g d x) → PartX s K p g d t κ x
          go (kept _)          _ = tt
          go (high _ _)        _ = tt
          go (cross _ _ _ _ _) r = r

        exact : Below → AboveL → (NodeRef 𝒮 𝓀 D nt → At PartX) × (At PartX → NodeRef 𝒮 𝓀 D nt)
        exact bl ab = need , split bl ab

        out : Below → AboveL → At PartX → NodeOut 𝒮 𝓀 D
        out bl ab cx = assemble 𝒮 𝓀 D nt (split bl ab cx)
```

## 出口去掉结点一条

`OutDN`, `OutRDN`: `QD.OutD`, `QD.OutRD` 除 `nodeE` 外的各条, 逐字照抄; 补上结点出口得原记录.

```agda
module Rest {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
            (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻
  open BL 𝔾 𝔻
  open QD 𝔾 𝔻

  module _ {j : Lv} (𝒮 : Sys j) where
    private module S = Sys 𝒮

    record OutDN (Le : T → T → Set) (𝒻 : S.FallLaw) : Set where
      open S.FallLaw 𝒻
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        upE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → (c : Ch a) → ∀ {t x} → R a t x → S.Q s K t x
              → Σ S.Cxt λ K′ → S.Bdˢ (step s c x) K′ × (∀ u → S.ap K′ u ≡ S.ap K (t ⊕ u))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o

    withN : ∀ {Le 𝓀 𝒻} {D : ∀ {a} → S.St a → Tr a → Set} → OutDN Le 𝒻 → NodeOut 𝒮 𝓀 D → OutD 𝒮 Le 𝓀 𝒻 D
    withN r n = record { zeroE = OutDN.zeroE r ; succE = OutDN.succE r ; limE = OutDN.limE r
                       ; upE = OutDN.upE r ; leE = OutDN.leE r ; nodeE = n }

  module _ {j : Lv} (𝒮 𝒜 : Sys j) (𝓀ᴬ : Sys.KeepLaw 𝒜) (ℯ : EmbLaw 𝒮 𝒜 𝓀ᴬ) where
    private module S = Sys 𝒮

    record OutRDN (Le : T → T → Set) (D : ∀ {a} → S.St a → Tr a → Set) : Set where
      field
        zeroE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C0 t → S.Q s K t x
        succE : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t x} → C1 t → R a (pred t) x → S.Q s K (pred t) x → S.Q s K t (sc x)
        limE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {t} → Cω t → Cω (S.ap K t) × (∀ n → fsn (S.ap K t) n ≡ S.ap K (fsn t n))
        leE   : ∀ {a} (s : S.St a) K → S.Bdˢ s K → ∀ {u t o} → Le u t → R j (S.ap K t) o → R j (S.ap K u) o
        embE  : ∀ {a} (s : S.St a) K → S.Bdˢ s K → EmbOutD 𝒮 𝒜 𝓀ᴬ ℯ Le D s K (EmbLaw.row ℯ s)

    withRN : ∀ {Le 𝓀} {D : ∀ {a} → S.St a → Tr a → Set} → OutRDN Le D → NodeOut 𝒮 𝓀 D → OutRD 𝒮 𝒜 𝓀ᴬ ℯ Le 𝓀 D
    withRN r n = record { zeroE = OutRDN.zeroE r ; succE = OutRDN.succE r ; limE = OutRDN.limE r
                        ; leE = OutRDN.leE r ; nodeE = n ; embE = OutRDN.embE r }
```
