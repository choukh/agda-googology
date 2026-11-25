# 主线折叠与产出端折叠的值关系族 (对 `Way′` 陈述)

验收文件. 编译定理, 无前提: 主线 [YiLeanFold](YiLeanFold.lagda.md) 的 `Ψ` 与 [YiProdFold](YiProdFold.lagda.md) 的消费端 `Ψᵖ` (对一切派发 `Dp` 与证据来源 `E`) 在不含 Ω 结点的公共上界 (`VRʷ`) 上互模拟 (`ΨRᵖ`), 合法性证明的路径对应 (`ΨLglRᵖ`, 输入不带标注); 自折叠 `Φ` 与主线的 `self` 折叠对应 (`ΦR`, `ΦLglR`).
`WR′` 把 `Way′` 的保留项与主线的 `keep` 对上, 搬运 `Mv` 要保关系、合法性的路径与第一位置的路径 (`MvR`, `byEq refl` 满足). 用处在 [YiWayBtbo](YiWayBtbo.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayRel where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanLegal as ML
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiZipWay as Z
open import OCF.Lean.YiCtxAnn using (noM; noP; mS; mL; mE; mB; pS; pL; pM; pB; cpA-no; dnA-no; lglA-no)
open import OCF.Lean.YiCtxFold using (Ev; SB; module FoldC)
import OCF.Lean.YiProdFold as P
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValPath
open import OCF.Lean.YiNextValLgl
open import OCF.Lean.YiDlVRel using (VRʷ; w0R; wsR; wlR; vLRʷ; shiftRʷ)
```

## 1 派发结果

```agda
MvR : (u : M.LF) (u′ j′ : N.LF) → Z.Mv u′ j′ → Set
MvR u u′ j′ t =
  (∀ η η′ → RR u u′ η η′ → RR u j′ η (Z.run t η′)) ×
  (∀ η η′ → RR u u′ η η′ → ∀ l l′ → LglR u u′ η η′ l l′ → LglR u j′ η (Z.run t η′) l (Z.run-lg t η′ l′)) ×
  (∀ {a b a′ b′} (e : M.Cp u a b) (e′ : N.Cp u′ a′ b′) → pCᴹ u e ≡ pCᴺ u′ e′ → pCᴹ u e ≡ pCᴺ j′ (Z.run-cp t e′))

mvR-eq : ∀ {u u′} → MvR u u′ u′ (Z.byEq refl)
mvR-eq = (λ η η′ d → d) , (λ η η′ d l l′ lr → lr) , (λ e e′ eq → eq)

WR′ : (m : M.LF) (m′ : N.LF) {j : M.LF} {j′ : N.LF} → MF.Way m j → Z.Way′ m′ j′ → Set
WR′ m m′ {j′ = j′} (MF.keep s refl) (Z.keep′ s′ t) = PR m m′ s s′ × MvR (MF.lev m s) (NB.lev m′ s′) j′ t
WR′ m m′ (MF.keep s refl) Z.fold′ = ⊥
WR′ m m′ MF.fold (Z.keep′ s′ t) = ⊥
WR′ m m′ MF.fold Z.fold′ = ⊤

substR′ : ∀ {a b c d : M.LF} {a′ b′ c′ d′ : N.LF} (p : a ≡ b) (q : c ≡ d) (p′ : a′ ≡ b′) (q′ : c′ ≡ d′)
  (w : MF.Way a c) (w′ : Z.Way′ a′ c′) → WR′ a a′ w w′ → WR′ b b′ (subst₂ MF.Way p q w) (subst₂ Z.Way′ p′ q′ w′)
substR′ refl refl refl refl w w′ h = h

XRᵖ : (m : M.LF) (m′ : N.LF) (k : M.LF) (k′ : N.LF) {Sb : N.Pre k′ → Set} → MF.Ext m k → P.Xm m′ k′ Sb → Set
XRᵖ m m′ k k′ x x′ = ∀ r r′ → PR k k′ r r′ → ∀ ε → WR′ m m′ (x r) (x′ r′ ε)
```

## 2 结点的两行 (对 `Way′`)

```agda
ΨnR′ : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : Z.Way′ m′ j′) → WR′ m m′ w w′ →
  ∀ {gm gm′ gk gk′} → (∀ η η′ → RR j j′ η η′ → RR m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) → RR m m′ (MF.Ψn m j w gm gk) (Z.Ψn′ m′ j′ w′ gm′ gk′)
ΨnR′ em ej (MF.keep p refl) (Z.keep′ p′ t) (q , mr) hm hk = nodeAtR em p p′ q lcBR (λ η η′ h → hm _ _ (proj₁ mr η η′ h))
ΨnR′ em ej MF.fold Z.fold′ q hm hk = rl (λ n → hm _ _ (chainR ej hk n))
ΨnR′ em ej (MF.keep p refl) Z.fold′ ()
ΨnR′ em ej MF.fold (Z.keep′ p′ t) ()

ΨNR′ : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : Z.Way′ m′ (NB.lev k′ r′)) → WR′ m m′ w w′ → ∀ {gm gm′ gk gk′} →
  (∀ η η′ → LayRel k k′ r r′ η η′ → RR m m′ (gm η) (gm′ η′)) →
  (∀ η η′ → LayRel k k′ r r′ η η′ → RR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′)) →
  RR m m′ (MF.ΨN m k r w gm gk) (Z.ΨN′ m′ k′ r′ w′ gm′ gk′)
ΨNR′ em lz () r′ q
ΨNR′ em (ls ek) (inj₁ _) (inj₁ _) q = ΨnR′ em ek
ΨNR′ em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNR′ em ek r r′ q
ΨNR′ em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNR′ em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNR′ em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNR′ em (ek n) r r′ q

pC-subst : ∀ {y : N.LF} {A : Set} (F : A → N.Raw y) {z u u′} (e : u ≡ u′) (q : N.Cp y z (F u)) →
  pCᴺ y (subst (λ w → N.Cp y z (F w)) e q) ≡ pCᴺ y q
pC-subst F refl q = refl

ΨnDnP′ : ∀ {m m′} → LR m m′ → ∀ {j j′} (w : MF.Way m j) (w′ : Z.Way′ m′ j′) → WR′ m m′ w w′ →
  ∀ gm gm′ gk gk′ {z z′} (q : M.Cp m z (gm M.G.top)) (q′ : N.Cp m′ z′ (gm′ N.G.top)) → pCᴹ m q ≡ pCᴺ m′ q′ →
  pDᴹ m (MF.Ψn m j w gm gk) (ML.Ψn-dn m j w gm gk q) ≡ pDᴺ m′ (Z.Ψn′ m′ j′ w′ gm′ gk′) (Z.Ψn′-dn m′ j′ w′ gm′ gk′ q′)
ΨnDnP′ em (MF.keep p refl) (Z.keep′ p′ t) (e , mr) gm gm′ gk gk′ {z′ = z′} q q′ eq =
  nodeAtDnP em p p′ e dbLc gm (λ η → gm′ (Z.run t η)) q (subst (λ u → N.Cp _ z′ (gm′ u)) (sym (Z.run-tp t)) q′)
    (trans eq (sym (pC-subst gm′ (sym (Z.run-tp t)) q′)))
ΨnDnP′ em MF.fold Z.fold′ e gm gm′ gk gk′ q q′ eq = cong (L 0 ∷_) eq
ΨnDnP′ em (MF.keep p refl) Z.fold′ ()
ΨnDnP′ em MF.fold (Z.keep′ p′ t) ()

ΨNDnP′ : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : Z.Way′ m′ (NB.lev k′ r′)) → WR′ m m′ w w′ → ∀ gm gm′ gk gk′ {z z′}
  (q : M.Cp m z (gm (M.Lay.tp (M.Lo k r)))) (q′ : N.Cp m′ z′ (gm′ (N.Lay.tp (N.Lo k′ r′)))) → pCᴹ m q ≡ pCᴺ m′ q′ →
  pDᴹ m (MF.ΨN m k r w gm gk) (ML.ΨN-dn m k r w gm gk q) ≡ pDᴺ m′ (Z.ΨN′ m′ k′ r′ w′ gm′ gk′) (Z.ΨN′-dn m′ k′ r′ w′ gm′ gk′ q′)
ΨNDnP′ em lz () r′ q
ΨNDnP′ em (ls ek) (inj₁ _) (inj₁ _) q = ΨnDnP′ em
ΨNDnP′ em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNDnP′ em ek r r′ q
ΨNDnP′ em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNDnP′ em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNDnP′ em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNDnP′ em (ek n) r r′ q

brRun : ∀ {u u′ j′ T T′} {t : Z.Mv u′ j′} → MvR u u′ j′ t → ∀ {g g′ l l′} → BrL u j′ T T′ g g′ l l′ →
  BrL u u′ T T′ g (λ η → g′ (Z.run t η)) l (Z.Br-run t g′ l′)
brRun {t = t} (r₁ , r₂ , r₃) (b₁ , b₂) =
  (λ η η′ d lη lη′ lr → b₁ η (Z.run t η′) (r₁ η η′ d) lη (Z.run-lg t η′ lη′) (r₂ η η′ d lη lη′ lr)) ,
  (λ η₁ η₁′ η₂ η₂′ d l₁ l₁′ e e′ l₂ l₂′ eq →
    b₂ η₁ (Z.run t η₁′) η₂ (Z.run t η₂′) (r₁ η₂ η₂′ d) l₁ (Z.run-lg t η₁′ l₁′) e (Z.run-cp t e′) l₂ (Z.run-lg t η₂′ l₂′)
      (r₃ e e′ eq))

ΨnLglR′ : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : Z.Way′ m′ j′) → WR′ m m′ w w′ →
  ∀ {gm gm′ gk gk′} hm hm′ → BrL j j′ m m′ gm gm′ hm hm′ →
  (hk : ∀ η η′ → RR j j′ η η′ → RR j j′ (gk η) (gk′ η′)) → ∀ {lk lk′} →
  (∀ η η′ → RR j j′ η η′ → ∀ l l′ → LglR j j′ η η′ l l′ → LglR j j′ (gk η) (gk′ η′) (lk η l) (lk′ η′ l′)) →
  LglR m m′ (MF.Ψn m j w gm gk) (Z.Ψn′ m′ j′ w′ gm′ gk′) (ML.Ψn-lgl m j w gm gk hm lk) (Z.Ψn′-lgl m′ j′ w′ gm′ gk′ hm′ lk′)
ΨnLglR′ em ej (MF.keep p refl) (Z.keep′ p′ t) (q , mr) hm hm′ br hk hl =
  nodeAtLglR em p p′ q lgbLc _ _ hm (Z.Br-run t _ hm′) (brRun mr br)
ΨnLglR′ em ej MF.fold Z.fold′ q hm hm′ br hk hl =
  (λ n → proj₂ br _ _ _ _ (chainR ej hk (suc n)) _ _ _ _ _ _ (addWkP ej dbLc _ _ (hk _ _ (chainR ej hk n)))) ,
  (λ n → proj₁ br _ _ (chainR ej hk n) _ _ (chainLglR ej hk hl n))
ΨnLglR′ em ej (MF.keep p refl) Z.fold′ ()
ΨnLglR′ em ej MF.fold (Z.keep′ p′ t) ()

ΨNLglR′ : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ →
  (w : MF.Way m (MF.lev k r)) (w′ : Z.Way′ m′ (NB.lev k′ r′)) → WR′ m m′ w w′ → ∀ {gm gm′ gk gk′} hm hm′ →
  BrR k k′ r r′ m m′ gm gm′ hm hm′ →
  (hk : ∀ η η′ → LayRel k k′ r r′ η η′ → RR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′)) → ∀ {lk lk′} →
  (∀ η η′ → LayRel k k′ r r′ η η′ → ∀ l l′ → LayLgl k k′ r r′ η η′ l l′ →
     LglR (MF.lev k r) (NB.lev k′ r′) (gk η) (gk′ η′) (lk η l) (lk′ η′ l′)) →
  LglR m m′ (MF.ΨN m k r w gm gk) (Z.ΨN′ m′ k′ r′ w′ gm′ gk′) (ML.ΨN-lgl m k r w gm gk hm lk) (Z.ΨN′-lgl m′ k′ r′ w′ gm′ gk′ hm′ lk′)
ΨNLglR′ em lz () r′ q
ΨNLglR′ em (ls ek) (inj₁ _) (inj₁ _) q = ΨnLglR′ em ek
ΨNLglR′ em (ls ek) (inj₂ r) (inj₂ r′) q = ΨNLglR′ em ek r r′ q
ΨNLglR′ em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNLglR′ em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNLglR′ em (ll ek) (n , r) (_ , r′) (refl , q) = ΨNLglR′ em (ek n) r r′ q
```

后继层号 `top` 那一句的 `Ψs`: 折叠时链是 `c`.

```agda
ΨsR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : Z.Way′ m′ j′) → WR′ m m′ w w′ →
  ∀ {gm gm′ gk c cp} → (∀ η η′ → RR j j′ η η′ → ∀ ρ → RR m m′ (gm η) (gm′ η′ ρ)) →
  (∀ n → RR j j′ (MF.chain j gk n) (c n)) → RR m m′ (MF.Ψn m j w gm gk) (P.Ψs m′ j′ w′ gm′ c cp)
ΨsR em ej (MF.keep p refl) (Z.keep′ p′ t) (q , mr) hm hc = nodeAtR em p p′ q lcBR (λ η η′ h → hm _ _ (proj₁ mr η η′ h) noP)
ΨsR em ej MF.fold Z.fold′ q hm hc = rl (λ n → hm _ _ (hc n) _)
ΨsR em ej (MF.keep p refl) Z.fold′ ()
ΨsR em ej MF.fold (Z.keep′ p′ t) ()

ΨsLglR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (w′ : Z.Way′ m′ j′) → WR′ m m′ w w′ →
  ∀ {gm gm′ gk c cp} hm b → BrL j j′ m m′ gm (λ η → gm′ η noP) hm b → ∀ {lk st lg} →
  (∀ n → pCᴹ m (proj₁ (ML.Ψn-lgl m j MF.fold gm gk hm lk) n) ≡ pCᴺ m′ (st n)) →
  (∀ n → LglR m m′ (gm (MF.chain j gk n)) (gm′ (c n) (cp n)) (proj₂ (ML.Ψn-lgl m j MF.fold gm gk hm lk) n) (lg n)) →
  LglR m m′ (MF.Ψn m j w gm gk) (P.Ψs m′ j′ w′ gm′ c cp) (ML.Ψn-lgl m j w gm gk hm lk) (P.Ψs-lgl m′ j′ w′ gm′ c cp b st lg)
ΨsLglR em ej (MF.keep p refl) (Z.keep′ p′ t) (q , mr) {gm′ = gm′} hm b br hs hl =
  nodeAtLglR em p p′ q lgbLc _ _ hm (Z.Br-run t (λ η → gm′ η noP) b) (brRun mr br)
ΨsLglR em ej MF.fold Z.fold′ q hm b br hs hl = hs , hl
ΨsLglR em ej (MF.keep p refl) Z.fold′ ()
ΨsLglR em ej MF.fold (Z.keep′ p′ t) ()
```

## 3 自折叠的派发

主线的结点由 `nodeAt` 沿槽位造, 产出端直接造 `G.lc (pos x r)`; 两边分支域的类型只在位置具体时相同, 所以按源位置的层 `RRL`, `LLL` 陈述. `WΦ`: 主线的派发在这里保留, 槽位相关, 搬运保关系、合法性的关系与路径.

```agda
RRL : (j : M.LF) (k′ : N.LF) (r′ : N.Pre k′) → M.Raw j → N.Lay.A (N.Lo k′ r′) → Set
RRL j N.zero ()
RRL j (N.suc k′) (inj₁ _) = RR j k′
RRL j (N.suc k′) (inj₂ r′) = RRL j k′ r′
RRL j (N.lim f′) (n , r′) = RRL j (f′ n) r′
RRL j (N.lc k′ g′) (η , _ , r′) = RRL j (g′ η) r′

LLL : (j : M.LF) (k′ : N.LF) (r′ : N.Pre k′) (η : M.Raw j) (a : N.Lay.A (N.Lo k′ r′)) →
  M.Lgl j η → N.Lay.lg (N.Lo k′ r′) a → Set
LLL j N.zero ()
LLL j (N.suc k′) (inj₁ _) = LglR j k′
LLL j (N.suc k′) (inj₂ r′) = LLL j k′ r′
LLL j (N.lim f′) (n , r′) = LLL j (f′ n) r′
LLL j (N.lc k′ g′) (η , _ , r′) = LLL j (g′ η) r′

MLg : (m′ : N.LF) (s′ : N.Pre m′) (k′ : N.LF) (r′ : N.Pre k′) → (N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) → Set
MLg m′ s′ k′ r′ mv = ∀ a → N.Lay.lg (N.Lo m′ s′) a → N.Lay.lg (N.Lo k′ r′) (mv a)

MLe : (m′ : N.LF) (s′ : N.Pre m′) (k′ : N.LF) (r′ : N.Pre k′) → (N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) → Set
MLe m′ s′ k′ r′ mv = ∀ {a b} → N.Le (N.Lo m′ s′) a b → N.Le (N.Lo k′ r′) (mv a) (mv b)

WΦ : (m : M.LF) (m′ : N.LF) {j : M.LF} → MF.Way m j → (s′ : N.Pre m′) (k′ : N.LF) (r′ : N.Pre k′)
  (mv : N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) → MLg m′ s′ k′ r′ mv → MLe m′ s′ k′ r′ mv → Set
WΦ m m′ (MF.keep s refl) s′ k′ r′ mv ml me = PR m m′ s s′ ×
  (∀ η a → RRL (MF.lev m s) m′ s′ η a → RRL (MF.lev m s) k′ r′ η (mv a)) ×
  (∀ η a → RRL (MF.lev m s) m′ s′ η a → ∀ lη la → LLL (MF.lev m s) m′ s′ η a lη la →
     LLL (MF.lev m s) k′ r′ η (mv a) lη (ml a la)) ×
  (∀ {a b a′ b′} (e : M.Cp (MF.lev m s) a b) (e′ : N.Le (N.Lo m′ s′) a′ b′) →
     pCᴹ (MF.lev m s) e ≡ pLeᴺ m′ s′ e′ → pCᴹ (MF.lev m s) e ≡ pLeᴺ k′ r′ (me e′))
WΦ m m′ MF.fold s′ k′ r′ mv ml me = ⊥

KW : (m : M.LF) {j : M.LF} → MF.Way m j → Set
KW m (MF.keep s refl) = ⊤
KW m MF.fold = ⊥

WΦ→KW : ∀ {m m′ j} (w : MF.Way m j) {s′ k′ r′ mv} {ml : MLg m′ s′ k′ r′ mv} {me : MLe m′ s′ k′ r′ mv} → WΦ m m′ w s′ k′ r′ mv ml me → KW m w
WΦ→KW (MF.keep s refl) h = tt
WΦ→KW MF.fold ()

WΦ-s₂ : ∀ {m m′ j} (w : MF.Way m j) {s′ k′ r′ mv} {ml : MLg m′ s′ k′ r′ mv} {me : MLe m′ s′ k′ r′ mv} →
  WΦ m m′ w s′ (N.suc k′) (inj₂ r′) mv ml me → WΦ m m′ w s′ k′ r′ mv ml me
WΦ-s₂ (MF.keep s refl) h = h
WΦ-s₂ MF.fold ()

WΦ-sℕ : ∀ {m m′ j} (w : MF.Way m j) {s′ f′ n r′ mv} {ml : MLg m′ s′ (f′ n) r′ mv} {me : MLe m′ s′ (f′ n) r′ mv} →
  WΦ m m′ w s′ (N.lim f′) (n , r′) mv ml me → WΦ m m′ w s′ (f′ n) r′ mv ml me
WΦ-sℕ (MF.keep s refl) h = h
WΦ-sℕ MF.fold ()

XΦ : (m : M.LF) (m′ : N.LF) (k : M.LF) (k′ : N.LF) → MF.Ext m k → P.PX m′ k′ → Set
XΦ m m′ k k′ x X = ∀ r r′ → PR k k′ r r′ → WΦ m m′ (x r) (P.pos X r′) k′ r′ (P.mvx X r′) (P.mlg X r′) (P.mle X r′)

selfΦ : ∀ {k k′} → XΦ k k′ k k′ (MF.self k) (P.selfR k′)
selfΦ r r′ q = q , (λ η a d → d) , (λ η a d lη la ll → ll) , (λ e e′ eq → eq)
```

主线一侧沿槽位造结点, 产出端一侧直接是结点.

```agda
nodeAtLcR : ∀ {T T′ m m′} → LR m m′ → ∀ p p′ → PR m m′ p p′ → ∀ {B B′} → BR T T′ m m′ B B′ → ∀ {g g′} →
  (∀ η a → RRL (MF.lev m p) m′ p′ η a → RR T T′ (g η) (g′ a)) → RR T T′ (MF.nodeAt m p B g) (B′ p′ g′)
nodeAtLcR lz () p′ q b h
nodeAtLcR (ls e) (inj₁ _) (inj₁ _) q b h = b (inj₁ tt) (inj₁ tt) tt h
nodeAtLcR (ls e) (inj₂ p) (inj₂ p′) q b h = nodeAtLcR e p p′ q (λ r r′ q′ → b (inj₂ r) (inj₂ r′) q′) h
nodeAtLcR (ls e) (inj₁ _) (inj₂ _) () b h
nodeAtLcR (ls e) (inj₂ _) (inj₁ _) () b h
nodeAtLcR (ll e) (n , p) (_ , p′) (refl , q) b h = nodeAtLcR (e n) p p′ q (λ r r′ q′ → b (n , r) (n , r′) (refl , q′)) h

BrLL : (j : M.LF) (m′ : N.LF) (p′ : N.Pre m′) (T : M.LF) (T′ : N.LF) (g : M.Raw j → M.Raw T)
  (g′ : N.Lay.A (N.Lo m′ p′) → N.Raw T′) → ML.Br (M.layer j) T g → NB.Br (N.Lo m′ p′) T′ g′ → Set
BrLL j m′ p′ T T′ g g′ l l′ =
  (∀ η a → RRL j m′ p′ η a → ∀ lη la → LLL j m′ p′ η a lη la →
     LglR T T′ (g η) (g′ a) (proj₁ l η lη) (proj₁ l′ a la)) ×
  (∀ η₁ a₁ η₂ a₂ → RRL j m′ p′ η₂ a₂ → ∀ l₁ l₁′ e e′ l₂ l₂′ → pCᴹ j e ≡ pLeᴺ m′ p′ e′ →
     pCᴹ T (proj₂ l η₁ η₂ l₁ e l₂) ≡ pCᴺ T′ (proj₂ l′ a₁ a₂ l₁′ e′ l₂′))

nodeAtLcLglR : ∀ {T T′ m m′} → LR m m′ → ∀ p p′ → PR m m′ p p′ → ∀ {B B′ b b′} → LgBR {T} {T′} {m} {m′} B B′ b b′ →
  ∀ g g′ br br′ → BrLL (MF.lev m p) m′ p′ T T′ g g′ br br′ →
  LglR T T′ (MF.nodeAt m p B g) (B′ p′ g′) (ML.nodeAt-lgl m p B b g br) (b′ p′ g′ br′)
nodeAtLcLglR lz () p′ e lb
nodeAtLcLglR (ls em) (inj₁ _) (inj₁ _) e lb = lb (inj₁ tt) (inj₁ tt) tt
nodeAtLcLglR (ls em) (inj₂ p) (inj₂ p′) e lb = nodeAtLcLglR em p p′ e (λ r r′ q → lb (inj₂ r) (inj₂ r′) q)
nodeAtLcLglR (ls em) (inj₁ _) (inj₂ _) () lb
nodeAtLcLglR (ls em) (inj₂ _) (inj₁ _) () lb
nodeAtLcLglR (ll em) (n , p) (_ , p′) (refl , e) lb = nodeAtLcLglR (em n) p p′ e (λ r r′ q → lb (n , r) (n , r′) (refl , q))

ΨnΦR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (s′ : N.Pre m′)
  (mv : N.Lay.A (N.Lo m′ s′) → N.Raw j′) (ml : MLg m′ s′ (N.suc j′) (inj₁ tt) mv) (me : MLe m′ s′ (N.suc j′) (inj₁ tt) mv) → WΦ m m′ w s′ (N.suc j′) (inj₁ tt) mv ml me →
  ∀ {gm gk} (g′ : N.Raw j′ → N.Raw m′) → (∀ η η′ → RR j j′ η η′ → RR m m′ (gm η) (g′ η′)) →
  RR m m′ (MF.Ψn m j w gm gk) (N.G.lc s′ (λ a → g′ (mv a)))
ΨnΦR em ej (MF.keep s refl) s′ mv ml me (q , t₁ , t₂ , t₃) g′ hm = nodeAtLcR em s s′ q lcBR (λ η a d → hm _ _ (t₁ η a d))
ΨnΦR em ej MF.fold s′ mv ml me () g′ hm

ΨNΦR : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ → (w : MF.Way m (MF.lev k r)) (s′ : N.Pre m′)
  (mv : N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) (ml : MLg m′ s′ k′ r′ mv) (me : MLe m′ s′ k′ r′ mv) → WΦ m m′ w s′ k′ r′ mv ml me →
  ∀ {gm gk} (g′ : N.Lay.A (N.Lo k′ r′) → N.Raw m′) → (∀ η η′ → LayRel k k′ r r′ η η′ → RR m m′ (gm η) (g′ η′)) →
  RR m m′ (MF.ΨN m k r w gm gk) (N.G.lc s′ (λ a → g′ (mv a)))
ΨNΦR em lz () r′ q
ΨNΦR em (ls ek) (inj₁ _) (inj₁ _) q = ΨnΦR em ek
ΨNΦR em (ls ek) (inj₂ r) (inj₂ r′) q w s′ mv ml me h = ΨNΦR em ek r r′ q w s′ mv ml me (WΦ-s₂ w h)
ΨNΦR em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNΦR em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNΦR em (ll ek) (n , r) (_ , r′) (refl , q) w s′ mv ml me h = ΨNΦR em (ek n) r r′ q w s′ mv ml me (WΦ-sℕ w h)

brMv : ∀ {T′ m′ s′ k′ r′} (mv : N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) → MLg m′ s′ k′ r′ mv → MLe m′ s′ k′ r′ mv →
  ∀ {g′} → NB.Br (N.Lo k′ r′) T′ g′ → NB.Br (N.Lo m′ s′) T′ (λ a → g′ (mv a))
brMv mv ml me (lg , mo) = (λ a l → lg (mv a) (ml a l)) , (λ a a′ l e l′ → mo (mv a) (mv a′) (ml a l) (me e) (ml a′ l′))

ΨnΦLglR : ∀ {m m′} → LR m m′ → ∀ {j j′} → LR j j′ → (w : MF.Way m j) (s′ : N.Pre m′)
  (mv : N.Lay.A (N.Lo m′ s′) → N.Raw j′) (ml : MLg m′ s′ (N.suc j′) (inj₁ tt) mv) (me : MLe m′ s′ (N.suc j′) (inj₁ tt) mv) → WΦ m m′ w s′ (N.suc j′) (inj₁ tt) mv ml me →
  ∀ {gm gk g′} hm hm′ → BrL j j′ m m′ gm g′ hm hm′ → ∀ lk →
  LglR m m′ (MF.Ψn m j w gm gk) (N.G.lc s′ (λ a → g′ (mv a))) (ML.Ψn-lgl m j w gm gk hm lk) (brMv mv ml me hm′)
ΨnΦLglR em ej (MF.keep s refl) s′ mv ml me (q , t₁ , t₂ , t₃) hm hm′ br lk =
  nodeAtLcLglR em s s′ q lgbLc _ _ hm (brMv mv ml me hm′)
    ((λ η a d lη la ll → proj₁ br η (mv a) (t₁ η a d) lη (ml a la) (t₂ η a d lη la ll)) ,
     (λ η₁ a₁ η₂ a₂ d l₁ l₁′ e e′ l₂ l₂′ eq →
       proj₂ br η₁ (mv a₁) η₂ (mv a₂) (t₁ η₂ a₂ d) l₁ (ml a₁ l₁′) e (me e′) l₂ (ml a₂ l₂′) (t₃ e e′ eq)))
ΨnΦLglR em ej MF.fold s′ mv ml me () hm hm′ br lk

ΨNΦLglR : ∀ {m m′} → LR m m′ → ∀ {k k′} → LR k k′ → ∀ r r′ → PR k k′ r r′ → (w : MF.Way m (MF.lev k r)) (s′ : N.Pre m′)
  (mv : N.Lay.A (N.Lo m′ s′) → N.Lay.A (N.Lo k′ r′)) (ml : MLg m′ s′ k′ r′ mv) (me : MLe m′ s′ k′ r′ mv) → WΦ m m′ w s′ k′ r′ mv ml me →
  ∀ {gm gk g′} hm hm′ → BrR k k′ r r′ m m′ gm g′ hm hm′ → ∀ lk →
  LglR m m′ (MF.ΨN m k r w gm gk) (N.G.lc s′ (λ a → g′ (mv a))) (ML.ΨN-lgl m k r w gm gk hm lk) (brMv mv ml me hm′)
ΨNΦLglR em lz () r′ q
ΨNΦLglR em (ls ek) (inj₁ _) (inj₁ _) q = ΨnΦLglR em ek
ΨNΦLglR em (ls ek) (inj₂ r) (inj₂ r′) q w s′ mv ml me h = ΨNΦLglR em ek r r′ q w s′ mv ml me (WΦ-s₂ w h)
ΨNΦLglR em (ls ek) (inj₁ _) (inj₂ _) ()
ΨNΦLglR em (ls ek) (inj₂ _) (inj₁ _) ()
ΨNΦLglR em (ll ek) (n , r) (_ , r′) (refl , q) w s′ mv ml me h = ΨNΦLglR em (ek n) r r′ q w s′ mv ml me (WΦ-sℕ w h)
```

主线保留时下行到结点的路径是 `C` 加上分支的路径 (单侧).

```agda
nodeAtC : ∀ {T} m p (B : M.Bld T m) (h : ML.DnB B) →
  (∀ r g {z} (q : M.Cp T z (g (M.Lay.tp (M.Lo m r)))) → pDᴹ T (B r g) (h r g q) ≡ C ∷ pCᴹ T q) →
  ∀ g {z} (q : M.Cp T z (g M.G.top)) → pDᴹ T (MF.nodeAt m p B g) (ML.nodeAt-dn m p B h g q) ≡ C ∷ pCᴹ T q
nodeAtC M.zero () B h hb
nodeAtC (M.suc k) (inj₁ _) B h hb g q = hb (inj₁ tt) g q
nodeAtC (M.suc k) (inj₂ p) B h hb = nodeAtC k p _ _ (λ r → hb (inj₂ r))
nodeAtC (M.lim f) (n , p) B h hb = nodeAtC (f n) p _ _ (λ r → hb (n , r))
nodeAtC (M.lc j g) (η , l , p) B h hb = nodeAtC (g η) p _ _ (λ r → hb (η , l , r))

ΨnC : ∀ m j (w : MF.Way m j) → KW m w → ∀ gm gk {z} (q : M.Cp m z (gm M.G.top)) →
  pDᴹ m (MF.Ψn m j w gm gk) (ML.Ψn-dn m j w gm gk q) ≡ C ∷ pCᴹ m q
ΨnC m _ (MF.keep p refl) tt gm gk q = nodeAtC m p M.G.lc ML.dnLc (λ r g q → refl) gm q
ΨnC m j MF.fold () gm gk q

ΨNC : ∀ m k r (w : MF.Way m (MF.lev k r)) → KW m w → ∀ gm gk {z} (q : M.Cp m z (gm (M.Lay.tp (M.Lo k r)))) →
  pDᴹ m (MF.ΨN m k r w gm gk) (ML.ΨN-dn m k r w gm gk q) ≡ C ∷ pCᴹ m q
ΨNC m M.zero ()
ΨNC m (M.suc k) (inj₁ _) = ΨnC m k
ΨNC m (M.suc k) (inj₂ r) = ΨNC m k r
ΨNC m (M.lim f) (n , r) = ΨNC m (f n) r
ΨNC m (M.lc j g) (η , _ , r) = ΨNC m (g η) r
```

## 4 对一切派发与证据来源

```agda
module WayRel (Dp : ∀ k K → Z.Ext′ k K) (E : Ev) where
  open FoldC Dp E using (cmpe)
  open P.Prod Dp E

  cmpRᵖ : ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ q q′ → PR k k′ q q′ → ∀ r r′ → PR k k′ r r′ → ∀ ε →
    WR′ (MF.lev k q) (NB.lev k′ q′) (MF.cmp V q r) (cmpe V′ q′ r′ ε)
  cmpRᵖ w0R () q′ e r r′ e′ ε
  cmpRᵖ (wsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₁ _) e′ ε = tt
  cmpRᵖ (wsR v) (inj₁ _) (inj₁ _) e (inj₂ r) (inj₂ r′) e′ ε = e′ , mvR-eq
  cmpRᵖ (wsR v) (inj₂ q) (inj₂ q′) e (inj₁ _) (inj₁ _) e′ ε = tt
  cmpRᵖ (wsR v) (inj₂ q) (inj₂ q′) e (inj₂ r) (inj₂ r′) e′ ε = cmpRᵖ v q q′ e r r′ e′ _
  cmpRᵖ (wsR v) (inj₁ _) (inj₂ _) () r r′ e′ ε
  cmpRᵖ (wsR v) (inj₂ _) (inj₁ _) () r r′ e′ ε
  cmpRᵖ (wsR v) (inj₁ _) (inj₁ _) e (inj₁ _) (inj₂ _) () ε
  cmpRᵖ (wsR v) (inj₁ _) (inj₁ _) e (inj₂ _) (inj₁ _) () ε
  cmpRᵖ (wsR v) (inj₂ _) (inj₂ _) e (inj₁ _) (inj₂ _) () ε
  cmpRᵖ (wsR v) (inj₂ _) (inj₂ _) e (inj₂ _) (inj₁ _) () ε
  cmpRᵖ (wlR {st = st} {st′ = st′} v h) (n , q) (_ , q′) (refl , e) (m , r) (_ , r′) (refl , e′) ε =
    substR′ (proj₂ (MF.shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (MF.shift st (≤⇒≤′ (m≤n⊔m n m)) r))
      (proj₂ (WL.shiftw st′ (≤⇒≤′ (m≤m⊔n n m)) q′)) (proj₂ (WL.shiftw st′ (≤⇒≤′ (m≤n⊔m n m)) r′)) _ _
      (cmpRᵖ (v (n ⊔ m)) _ _ (shiftRʷ h (≤⇒≤′ (m≤m⊔n n m)) q q′ e) _ _ (shiftRʷ h (≤⇒≤′ (m≤n⊔m n m)) r r′ e′) _)
```

自折叠 `Φ` 与主线的 `self` 折叠.

```agda
  ΦR : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {x X} → XΦ m m′ k k′ x X →
    ∀ {ξ ξ′} → RR k k′ ξ ξ′ → RR m m′ (MF.Ψ m V x ξ) (Φ m′ V′ X ξ′)
  ΦR em v xr rz = rt
  ΦR em v xr (rs d) = succR em (ΦR em v xr d)
  ΦR em v xr (rl d) = rl (λ n → ΦR em v xr (d n))
  ΦR em {V′ = V′} v {x} {X} xr (rc {r = r} {r′ = r′} {g′ = g′} q h) =
    ΨNΦR em (vLRʷ v) r r′ q (x r) (P.pos X r′) (P.mvx X r′) (P.mlg X r′) (P.mle X r′) (xr r r′ q)
      (λ η → Φ _ V′ X (g′ η)) (λ η η′ h′ → ΦR em v xr (h η η′ h′))
  ΦR em w0R xr rt = succR em rt
  ΦR em (wsR {V′ = V₀′} v) {x} {X} xr rt =
    ΨnΦR em (vLRʷ v) (x (inj₁ tt)) (P.pos X (inj₁ tt)) (P.mvx X (inj₁ tt)) (P.mlg X (inj₁ tt)) (P.mle X (inj₁ tt))
      (xr (inj₁ tt) (inj₁ tt) tt) (λ η → Φ _ V₀′ (P.sub₂ X) η)
      (λ η η′ h → ΦR em v (λ r r′ e → WΦ-s₂ (x (inj₂ r)) (xr (inj₂ r) (inj₂ r′) e)) h)
  ΦR em (wlR v s) {x} {X} xr rt =
    rl (psumR em (λ n → ΦR em (v n) (λ r r′ e → WΦ-sℕ (x (n , r)) (xr (n , r) (n , r′) (refl , e))) rt))

  ΦCpP : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {x X} → XΦ m m′ k k′ x X →
    ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Cp k ξ ζ) (p′ : N.Cp k′ ξ′ ζ′) → pCᴹ k p ≡ pCᴺ k′ p′ →
    pCᴹ m (ML.Ψ-cp m V x p) ≡ pCᴺ m′ (Φ-cp m′ V′ X p′)
  ΦDnP : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {x X} → XΦ m m′ k k′ x X →
    ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Dn k ξ ζ) (p′ : N.Dn k′ ξ′ ζ′) → pDᴹ k ζ p ≡ pDᴺ k′ ζ′ p′ →
    pDᴹ m (MF.Ψ m V x ζ) (ML.Ψ-dn m V x ζ p) ≡ pDᴺ m′ (Φ m′ V′ X ζ′) (Φ-dn m′ V′ X ζ′ p′)

  ΦCpP em v xr d (inj₁ refl) (inj₁ refl) eq = refl
  ΦCpP em v xr d (inj₂ p) (inj₂ p′) eq = cong (D ∷_) (ΦDnP em v xr d p p′ (cong tl eq))
  ΦCpP em v xr d (inj₁ refl) (inj₂ p′) ()
  ΦCpP em v xr d (inj₂ p) (inj₁ refl) ()

  ΦDnP em v xr (rs d) p p′ eq = cong (L 0 ∷_) (ΦCpP em v xr d p p′ (cong tl eq))
  ΦDnP em v xr (rl d) (n , p) (n′ , p′) eq with cong ix eq
  ... | refl = cong (L n ∷_) (ΦCpP em v xr (d n) p p′ (cong tl eq))
  ΦDnP em {V = V} {V′} v {x} {X} xr (rc {r = r} {r′ = r′} {g = g} {g′ = g′} q h) p p′ eq =
    trans (ΨNC _ _ r (x r) (WΦ→KW (x r) (xr r r′ q)) _ _ (ML.Ψ-cp _ V x p))
      (cong (C ∷_) (trans (ΦCpP em v xr (h _ _ (tpR (vLRʷ v) r r′ q)) p p′ (cong tl eq))
        (sym (pC-subst (λ u → Φ _ V′ X (g′ u)) (sym (P.mtp X r′)) (Φ-cp _ V′ X p′)))))

  ΦLglR : ∀ {m m′} (em : LR m m′) {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} (v : VRʷ V V′) {x X} (xr : XΦ m m′ k k′ x X)
    {ξ ξ′} (d : RR k k′ ξ ξ′) {l l′} → LglR k k′ ξ ξ′ l l′ →
    LglR m m′ (MF.Ψ m V x ξ) (Φ m′ V′ X ξ′) (ML.Ψ-lgl m V x ξ l) (Φ-lgl m′ V′ X ξ′ l′)
  ΦLglR em v xr rz lr = tt
  ΦLglR em v xr (rs d) lr = succLglR em (ΦR em v xr d) (ΦLglR em v xr d lr)
  ΦLglR em v xr (rl d) lr = (λ n → ΦCpP em v xr (d (suc n)) _ _ (proj₁ lr n)) , (λ n → ΦLglR em v xr (d n) (proj₂ lr n))
  ΦLglR em {V′ = V′} v {x} {X} xr (rc {r = r} {r′ = r′} {g′ = g′} q h) {l′ = l′} lr =
    ΨNΦLglR em (vLRʷ v) r r′ q (x r) (P.pos X r′) (P.mvx X r′) (P.mlg X r′) (P.mle X r′) (xr r r′ q) _
      ((λ η l → Φ-lgl _ V′ X (g′ η) (proj₁ l′ η l)) , (λ η η′ l e l₂ → Φ-cp _ V′ X (proj₂ l′ η η′ l e l₂)))
      ((λ η η′ hr lη lη′ ll → ΦLglR em v xr (h η η′ hr) (proj₁ lr η η′ hr lη lη′ ll)) ,
       (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
         ΦCpP em v xr (h η₂ η₂′ hr₂) _ _ (proj₂ lr η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq)))
      _
  ΦLglR em w0R xr rt lr = succLglR em rt tt
  ΦLglR em (wsR {V′ = V₀′} v) {x} {X} xr rt lr =
    ΨnΦLglR em (vLRʷ v) (x (inj₁ tt)) (P.pos X (inj₁ tt)) (P.mvx X (inj₁ tt)) (P.mlg X (inj₁ tt)) (P.mle X (inj₁ tt))
      (xr (inj₁ tt) (inj₁ tt) tt) _
      ((λ η l → Φ-lgl _ V₀′ (P.sub₂ X) η l) , (λ η η′ l e l₂ → Φ-cp _ V₀′ (P.sub₂ X) e))
      ((λ η η′ hr lη lη′ ll → ΦLglR em v (λ r r′ e → WΦ-s₂ (x (inj₂ r)) (xr (inj₂ r) (inj₂ r′) e)) hr ll) ,
       (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
         ΦCpP em v (λ r r′ e → WΦ-s₂ (x (inj₂ r)) (xr (inj₂ r) (inj₂ r′) e)) hr₂ u u′ eq))
      _
  ΦLglR em (wlR v s) {x} {X} xr rt lr =
    psumLglR em (λ n → ΦR em (v n) (λ r r′ e → WΦ-sℕ (x (n , r)) (xr (n , r) (n , r′) (refl , e))) rt)
      (λ n → ΦLglR em (v n) (λ r r′ e → WΦ-sℕ (x (n , r)) (xr (n , r) (n , r′) (refl , e))) rt tt)

  chR : ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} (v : VRʷ V V′) n →
    RR k k′ (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n) (chT k′ V′ n)
  chR v zero = rt
  chR v (suc n) = plusR (vLRʷ v) (chR v n) (ΦR (vLRʷ v) v selfΦ (chR v n))

  chLR : ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} (v : VRʷ V V′) n →
    LglR k k′ (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n) (chT k′ V′ n)
      (ML.chain-lgl k (λ η → MF.Ψ k V (MF.self k) η) (λ η l → ML.Ψ-lgl k V (MF.self k) η l) n) (chLb k′ V′ n)
  chLR v zero = tt
  chLR v (suc n) = plusLglR (vLRʷ v) (chR v n) (ΦR (vLRʷ v) v selfΦ (chR v n)) (chLR v n)
    (ΦLglR (vLRʷ v) v selfΦ (chR v n) (chLR v n))
```

消费端. 输入不带标注 (`noM`, `noP`); 不含 Ω 结点的层号上链点也不带标注, 所以 `top` 那一句按内层的层号分三种 (`topPL`).

```agda
  ΨRᵖ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {Sb x x′} → XRᵖ m m′ k k′ {Sb} x x′ →
    ∀ {ξ ξ′} → RR k k′ ξ ξ′ → ∀ μ π → RR m m′ (MF.Ψ m V x ξ) (Ψᵖ m′ V′ Sb x′ ξ′ μ π)
  ΨRᵖ em v xr rz μ π = rt
  ΨRᵖ em v xr (rs d) μ π = succR em (ΨRᵖ em v xr d (mS μ) (pS π))
  ΨRᵖ em v xr (rl d) μ π = rl (λ n → ΨRᵖ em v xr (d n) (mL μ n) (pL π n))
  ΨRᵖ em v {Sb} {x} {x′} xr (rc {r = r} {r′ = r′} q h) μ π =
    ΨNR′ em (vLRʷ v) r r′ q (x r) (x′ r′ (mE μ)) (xr r r′ q (mE μ))
      (λ η η′ h′ → ΨRᵖ em v xr (h η η′ h′) (mB μ η′) (pB π η′))
      (λ η η′ h′ → ΨRᵖ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRᵖ v r r′ q q₁ q₁′ e) (h η η′ h′) (pM π η′) (pB π η′))
  ΨRᵖ em w0R xr rt μ π = succR em rt
  ΨRᵖ em (wsR v) {x = x} {x′} xr rt μ π =
    ΨsR em (vLRʷ v) (x (inj₁ tt)) (x′ (inj₁ tt) nothing) (xr (inj₁ tt) (inj₁ tt) tt nothing)
      (λ η η′ h ρ → ΨRᵖ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) h noM ρ) (chR v)
  ΨRᵖ em (wlR v s) xr rt μ π = rl (psumR em (λ n → ΨRᵖ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt noM noP))

  ΨCpPᵖ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {Sb x x′} → XRᵖ m m′ k k′ {Sb} x x′ →
    ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Cp k ξ ζ) (p′ : N.Cp k′ ξ′ ζ′) → pCᴹ k p ≡ pCᴺ k′ p′ →
    pCᴹ m (ML.Ψ-cp m V x p) ≡ pCᴺ m′ (Ψᵖ-cp m′ V′ Sb x′ (cpA-no Sb p′))
  ΨDnPᵖ : ∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {Sb x x′} → XRᵖ m m′ k k′ {Sb} x x′ →
    ∀ {ξ ξ′ ζ ζ′} → RR k k′ ζ ζ′ → (p : M.Dn k ξ ζ) (p′ : N.Dn k′ ξ′ ζ′) → pDᴹ k ζ p ≡ pDᴺ k′ ζ′ p′ →
    pDᴹ m (MF.Ψ m V x ζ) (ML.Ψ-dn m V x ζ p) ≡
    pDᴺ m′ (Ψᵖ m′ V′ Sb x′ ζ′ noM noP) (Ψᵖ-dn m′ V′ Sb x′ (ξ′ , noM , noP) ζ′ noM noP (dnA-no Sb ζ′ p′))

  ΨCpPᵖ em v xr d (inj₁ refl) (inj₁ refl) eq = refl
  ΨCpPᵖ em v xr d (inj₂ p) (inj₂ p′) eq = cong (D ∷_) (ΨDnPᵖ em v xr d p p′ (cong tl eq))
  ΨCpPᵖ em v xr d (inj₁ refl) (inj₂ p′) ()
  ΨCpPᵖ em v xr d (inj₂ p) (inj₁ refl) ()

  ΨDnPᵖ em v xr (rs d) p p′ eq = cong (L 0 ∷_) (ΨCpPᵖ em v xr d p p′ (cong tl eq))
  ΨDnPᵖ em v xr (rl d) (n , p) (n′ , p′) eq with cong ix eq
  ... | refl = cong (L n ∷_) (ΨCpPᵖ em v xr (d n) p p′ (cong tl eq))
  ΨDnPᵖ em {V = V} {V′} v {Sb} {x} {x′} xr (rc {r = r} {r′ = r′} {g = g} {g′ = g′} q h) p p′ eq =
    ΨNDnP′ em (vLRʷ v) r r′ q (x r) (x′ r′ nothing) (xr r r′ q nothing)
      (λ η → MF.Ψ _ V x (g η)) (λ η → Ψᵖ _ V′ Sb x′ (g′ η) noM noP)
      (λ η → MF.Ψ (MF.lev _ r) V (MF.cmp V r) (g η)) (λ η → Ψᵖ (NB.lev _ r′) V′ (SB _ r′) (cmpe V′ r′) (g′ η) noM noP)
      (ML.Ψ-cp _ V x p) (Ψᵖ-cp _ V′ Sb x′ (cpA-no Sb p′)) (ΨCpPᵖ em v xr (h _ _ (tpR (vLRʷ v) r r′ q)) p p′ (cong tl eq))

  ΨLglRᵖ : ∀ {m m′} (em : LR m m′) {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} (v : VRʷ V V′) {Sb x x′}
    (xr : XRᵖ m m′ k k′ {Sb} x x′) {ξ ξ′} (d : RR k k′ ξ ξ′) {l l′} → LglR k k′ ξ ξ′ l l′ →
    LglR m m′ (MF.Ψ m V x ξ) (Ψᵖ m′ V′ Sb x′ ξ′ noM noP) (ML.Ψ-lgl m V x ξ l)
      (Ψᵖ-lgl m′ V′ Sb x′ ξ′ noM noP (lglA-no Sb ξ′ l′))
  topPL : ∀ {m m′} (em : LR m m′) {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} (v : VRʷ V V′) {Sb x x′}
    (xr : XRᵖ m m′ k k′ {Sb} x x′) n →
    (pCᴹ m (ML.Ψ-cp m V x (ML.plus-weak k (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n)
        (MF.Ψ k V (MF.self k) (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n))))
      ≡ pCᴺ m′ (Ψᵖ-cp m′ V′ Sb x′ (chC k′ V′ Sb n))) ×
    LglR m m′ (MF.Ψ m V x (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n)) (Ψᵖ m′ V′ Sb x′ (chT k′ V′ n) noM (chP k′ V′ n))
      (ML.Ψ-lgl m V x _ (ML.chain-lgl k (λ η → MF.Ψ k V (MF.self k) η) (λ η l → ML.Ψ-lgl k V (MF.self k) η l) n))
      (Ψᵖ-lgl m′ V′ Sb x′ (chT k′ V′ n) noM (chP k′ V′ n) (chL k′ V′ Sb n))

  ΨLglRᵖ em v xr rz lr = tt
  ΨLglRᵖ em v xr (rs d) lr = succLglR em (ΨRᵖ em v xr d noM noP) (ΨLglRᵖ em v xr d lr)
  ΨLglRᵖ em v xr (rl d) lr =
    (λ n → ΨCpPᵖ em v xr (d (suc n)) _ _ (proj₁ lr n)) , (λ n → ΨLglRᵖ em v xr (d n) (proj₂ lr n))
  ΨLglRᵖ em v {Sb} {x} {x′} xr (rc {r = r} {r′ = r′} q h) lr =
    ΨNLglR′ em (vLRʷ v) r r′ q (x r) (x′ r′ nothing) (xr r r′ q nothing) _ _
      ((λ η η′ hr lη lη′ ll → ΨLglRᵖ em v xr (h η η′ hr) (proj₁ lr η η′ hr lη lη′ ll)) ,
       (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq →
         ΨCpPᵖ em v xr (h η₂ η₂′ hr₂) _ _ (proj₂ lr η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq)))
      (λ η η′ hr → ΨRᵖ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRᵖ v r r′ q q₁ q₁′ e) (h η η′ hr) noM noP)
      (λ η η′ hr lη lη′ ll → ΨLglRᵖ (levR (vLRʷ v) r r′ q) v (λ q₁ q₁′ e → cmpRᵖ v r r′ q q₁ q₁′ e) (h η η′ hr)
         (proj₁ lr η η′ hr lη lη′ ll))
  ΨLglRᵖ em w0R xr rt lr = succLglR em rt tt
  ΨLglRᵖ em (wsR v) {x = x} {x′} xr rt lr =
    ΨsLglR em (vLRʷ v) (x (inj₁ tt)) (x′ (inj₁ tt) nothing) (xr (inj₁ tt) (inj₁ tt) tt nothing) _ _
      ((λ η η′ hr lη lη′ ll → ΨLglRᵖ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr ll) ,
       (λ η₁ η₁′ η₂ η₂′ hr₂ l₁ l₁′ u u′ l₂ l₂′ eq → ΨCpPᵖ em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) hr₂ u u′ eq))
      (λ n → proj₁ (topPL em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) n))
      (λ n → proj₂ (topPL em v (λ r r′ e → xr (inj₂ r) (inj₂ r′) e) n))
  ΨLglRᵖ em (wlR v s) xr rt lr =
    psumLglR em (λ n → ΨRᵖ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt noM noP)
      (λ n → ΨLglRᵖ em (v n) (λ r r′ e → xr (n , r) (n , r′) (refl , e)) rt tt)

  topPL em v@w0R xr n =
    ΨCpPᵖ em v xr (chR v (suc n)) _ _ (addWkP (vLRʷ v) dbLc _ _ (ΦR (vLRʷ v) v selfΦ (chR v n))) ,
    ΨLglRᵖ em v xr (chR v n) (chLR v n)
  topPL em v@(wsR _) xr n =
    ΨCpPᵖ em v xr (chR v (suc n)) _ _ (addWkP (vLRʷ v) dbLc _ _ (ΦR (vLRʷ v) v selfΦ (chR v n))) ,
    ΨLglRᵖ em v xr (chR v n) (chLR v n)
  topPL em v@(wlR _ _) xr n =
    ΨCpPᵖ em v xr (chR v (suc n)) _ _ (addWkP (vLRʷ v) dbLc _ _ (ΦR (vLRʷ v) v selfΦ (chR v n))) ,
    ΨLglRᵖ em v xr (chR v n) (chLR v n)
```
