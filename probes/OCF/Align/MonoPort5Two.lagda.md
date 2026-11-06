# 第三站 (五): 实例 3 的第 2 层语义

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 第 2 层的上下文不被读 (取 $\top$). 两种节点:
>
> - **第 1 层节点** (`niS₂₁`): $T_0$, $T_1$ 上上升, 由第 1 层的链 ([MonoPort5Chn](MonoPort5Chn.lagda.md) 的 `chainG`, 链点按 $\sqsubseteq_1$, 一步用 `snd₁`), 两个目标的输出都是链段输出的极限 (`lm`, `nl⊑`); $T_2$ 上保留, 分支 "先在第 1 层走坐标、再在第 2 层走分支" (`brn₁`, 对一切第 1 层动作).
> - **第 0 层节点** (`niS₂₀`): $T_0$ 上上升 (`chain₀ᴳ`); $T_1$, $T_2$ 上保留 (`brn₀`). 保留到 $T_1$ 的节点是第 1 层的节点, 坐标按 $\sqsubseteq_0$, 正是 $\sqsubseteq_1$ 的节点构造子.
> - **`snd₂`**: $x\sqsubseteq_2x'$ ⇒ 两动作的第 2 层语义.
>
> 节点一步的形状: 节点层 $k$ 对目标层 $e$, $e\le k$ 上升 (层 $k$ 的链, 一步用层 $k$ 的 `snd`), $e>k$ 保留 (层 $k$ 的 `snd` 走坐标, 再用分支的语义). `niS₁`, `niS₂₁`, `niS₂₀` 是这一句话的三个实例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort5Two {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (D; hz; hs; hself; hsuc; ss; accL; n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.MonoPort5Rel lW
open import OCF.Align.MonoPort5One lW using (module Z0; ac₁; Cx₁; In₁; module C1; module K1; cl₁; preL≡; brn₀; Sem₁; snd₁)
import OCF.Align.MonoPort5Chn as Chn

ac₂ = accL L2

module C2 = Chn Λ₃ tt lW k0 O₃ L2 ac₂ k2 (λ _ _ → ⊤) (λ _ _ → ⊤)
module K2 = C2.K

cl₂ : K2.CxLaws
cl₂ = record { cxL = λ _ → K2.cx tt ; cxR = λ _ → K2.cx tt ; cx⨾ = λ _ _ _ _ → K2.cx tt ; cx0ˡ = λ _ _ → K2.cx tt ; cx0ʳ = λ _ _ → K2.cx tt
             ; cxas = λ _ _ _ _ → K2.cx tt ; cxas′ = λ _ _ _ _ → K2.cx tt ; cxpre = λ _ _ _ _ _ → K2.cx tt ; cxlim = λ _ _ _ _ → K2.cx tt }

open K2.Steps cl₂

Sem₂ : D L2 W → D L2 W → Set
Sem₂ x x′ = ∀ (Aᵢ Aⱼ : K2.Act) → K2.HA Aᵢ Aᵢ → K2.HA Aⱼ Aⱼ → K2.HA Aᵢ Aⱼ → K2.Sem Aᵢ Aⱼ {tt} {tt} x x′
```

## §1 第 1 层节点的分支与链

```agda
Sv₁ : K1.Act → P.St W → D L1 W → P.St W
Sv₁ i Y z = P.cv C.self Y G.⊕ K1.Run (P.Ig↾ C.self i) z tt n0 (P.cv C.self Y)

cx0₁ : K1.Cx n0 n0
cx0₁ = K1.cx (R1.n0⊑ , (R1.n0⊑ , R1.n0⊑))

brn₁ : ∀ (i j : K1.Act) → K1.HA i i → K1.HA j j → K1.HA i j → ∀ (Y Y′ : P.St W) → K1.Good Y → K1.Good Y′ → K1.SRel Y Y′ →
       ∀ (z z′ : D L1 W) → Low₂ (ss hself) z z′ → i C.self lW z (Sv₁ i Y z) ≼ j C.self lW z′ (Sv₁ j Y′ z′)
brn₁ i j hi hj hij Y Y′ g g′ s z z′ (le , (oz , oz′)) = proj₂ (hij z z′ azero azero S S′ (K1.cx (le , (oz , oz′))) gS gS′ sS z≤)
  where
  i′ = P.Ig↾ C.self i
  j′ = P.Ig↾ C.self j
  Y₁ = P.cv C.self Y
  Y₁′ = P.cv C.self Y′
  Δ = K1.Run i′ z tt n0 Y₁
  Δ′ = K1.Run j′ z′ tt n0 Y₁′
  S = Y₁ G.⊕ Δ
  S′ = Y₁′ G.⊕ Δ′
  o = snd₁ le i′ j′ hi hj hij tt tt n0 n0 (G.vY Y) (G.vY Y′) Y₁ Y₁′ cx0₁ g g′ s (proj₁ s)
  rΔ = proj₂ (snd₁ (R1.OkRf oz) i′ i′ hi hi hi tt tt n0 n0 azero azero Y₁ Y₁ cx0₁ g g (K1.sr {Y₁} g) z≤)
  rΔ′ = proj₂ (snd₁ (R1.OkRf oz′) j′ j′ hj hj hj tt tt n0 n0 azero azero Y₁′ Y₁′ cx0₁ g′ g′ (K1.sr {Y₁′} g′) z≤)
  gS = K1.G⊕ {Y₁} {Δ} g rΔ
  gS′ = K1.G⊕ {Y₁′} {Δ′} g′ rΔ′
  sS = K1.S⊕ {Y₁} {Y₁′} {Δ} {Δ′} g g′ s o

-- 第 1 层的链: 链点按 ⊑₁, 上下文按 Cx₁
cxc₁ : ∀ {c c′ δ δ′} → K1.Cx c c′ → δ ⊑₁ δ′ → Rf₁ δ → Rf₁ δ′ → K1.Cx (c ⨾ δ) (c′ ⨾ δ′)
cxc₁ (K1.cx (hc , (oc , oc′))) pd pdd pdd′ = K1.cx (R1.⨾⊑ (R1.OkRf oc) (R1.OkRf oc′) hc pd , ((oc , pdd) , (oc′ , pdd′)))

module CH1 = C1.Chain cl₁ _⊑₁_ snd₁ (λ h → proj₁ (proj₂ h)) cx0₁ cxc₁

Br₂₁ Br₂₀ : Set
Br₂₁ = ∀ {W′} → W ⊲ W′ → Lg W′ → D L1 W′ → D L2 W′
Br₂₀ = ∀ {W′} → W ⊲ W′ → Lg W′ → D hz W′ → D L2 W′

Ai₂₁ : K2.Act → Br₂₁ → D L2 W → K1.Act
Ai₂₁ A₀ u w = P.Ai ac₂ ac₁ (ss hself) u C.self k1 k2 A₀ w

Ai₂₀ : K2.Act → Br₂₀ → D L2 W → Z0.Act
Ai₂₀ A₀ u w = P.Ai ac₂ (accL hz) (ss (hsuc hself)) u C.self k0 k2 A₀ w

hAi₂₁ : ∀ (Aᵢ Aⱼ : K2.Act) → K2.HA Aᵢ Aᵢ → K2.HA Aⱼ Aⱼ → K2.HA Aᵢ Aⱼ → ∀ {u u′ : Br₂₁} →
        (∀ z z′ → Low₂ (ss hself) z z′ → Sem₂ (u C.self lW z) (u′ C.self lW z′)) → ∀ w w′ → K1.HA (Ai₂₁ Aᵢ u w) (Ai₂₁ Aⱼ u′ w′)
hAi₂₁ Aᵢ Aⱼ hi hj hij sc w w′ z z′ c c′ Y Y′ (K1.cx l) g g′ s cb =
  sc z z′ l (P.Ig↾ C.self Aᵢ) (P.Ig↾ C.self Aⱼ) hi hj hij tt tt _ _ c c′ Y Y′ (K2.cx tt) g g′ s cb

hAi₂₀ : ∀ (Aᵢ Aⱼ : K2.Act) → K2.HA Aᵢ Aᵢ → K2.HA Aⱼ Aⱼ → K2.HA Aᵢ Aⱼ → ∀ {u u′ : Br₂₀} →
        (∀ z z′ → z ⊑₀ z′ → Sem₂ (u C.self lW z) (u′ C.self lW z′)) → ∀ w w′ → Z0.HA (Ai₂₀ Aᵢ u w) (Ai₂₀ Aⱼ u′ w′)
hAi₂₀ Aᵢ Aⱼ hi hj hij sc w w′ z z′ c c′ Y Y′ (Z0.cx l) g g′ s cb =
  sc z z′ l (P.Ig↾ C.self Aᵢ) (P.Ig↾ C.self Aⱼ) hi hj hij tt tt _ _ c c′ Y Y′ (K2.cx tt) g g′ s cb
```

## §2 两种节点一步

```agda
niS₂₁ : ∀ (Aᵢ Aⱼ : K2.Act) (hi : K2.HA Aᵢ Aᵢ) (hj : K2.HA Aⱼ Aⱼ) (hij : K2.HA Aᵢ Aⱼ) {u u′ : Br₂₁} →
        (∀ z z′ → Low₂ (ss hself) z z′ → Sem₂ (u C.self lW z) (u C.self lW z′)) →
        (∀ z z′ → Low₂ (ss hself) z z′ → Sem₂ (u′ C.self lW z) (u′ C.self lW z′)) →
        (∀ z z′ → Low₂ (ss hself) z z′ → Sem₂ (u C.self lW z) (u′ C.self lW z′)) → K2.Sem Aᵢ Aⱼ {tt} {tt} (ni (ss hself) u) (ni (ss hself) u′)
niS₂₁ Aᵢ Aⱼ hi hj hij {u} {u′} su su′ sc tt tt w w′ c c′ Y Y′ _ g g′ s cb =
  proj₁ chx ,
  (lm (λ n → proj₁ (proj₂ chx n)) ,
   (R1.nl⊑ (λ n → proj₁ (proj₂ (proj₂ chi n))) (λ n → proj₁ (proj₂ (proj₂ chj n))) (λ n → proj₁ (proj₂ (proj₂ chx n))) ,
    R2.ni⊑ (ss hself) (λ z z′ le → proj₂ (proj₂ (brn₁ i i h0 h0 h0 Y Y g g (K1.sr {Y} g) z z′ le)))
                      (λ z z′ le → proj₂ (proj₂ (brn₁ j j h1 h1 h1 Y′ Y′ g′ g′ (K1.sr {Y′} g′) z z′ le)))
                      (λ z z′ le → proj₂ (proj₂ (brn₁ i j h0 h1 hx Y Y′ g g′ s z z′ le)))))
  where
  i = Ai₂₁ Aᵢ u w
  j = Ai₂₁ Aⱼ u′ w′
  h0 = hAi₂₁ Aᵢ Aᵢ hi hi hi {u} {u} su w w
  h1 = hAi₂₁ Aⱼ Aⱼ hj hj hj {u′} {u′} su′ w′ w′
  hx = hAi₂₁ Aᵢ Aⱼ hi hj hij {u} {u′} sc w w′
  chx = CH1.chainG i j h0 h1 hx Y Y′ c c′ g g′ s cb
  chi = CH1.chainG i i h0 h0 h0 Y Y c c g g (K1.sr {Y} g) (≤-refl c)
  chj = CH1.chainG j j h1 h1 h1 Y′ Y′ c′ c′ g′ g′ (K1.sr {Y′} g′) (≤-refl c′)

niS₂₀ : ∀ (Aᵢ Aⱼ : K2.Act) (hi : K2.HA Aᵢ Aᵢ) (hj : K2.HA Aⱼ Aⱼ) (hij : K2.HA Aᵢ Aⱼ) {u u′ : Br₂₀} →
        (∀ z z′ → z ⊑₀ z′ → Sem₂ (u C.self lW z) (u C.self lW z′)) →
        (∀ z z′ → z ⊑₀ z′ → Sem₂ (u′ C.self lW z) (u′ C.self lW z′)) →
        (∀ z z′ → z ⊑₀ z′ → Sem₂ (u C.self lW z) (u′ C.self lW z′)) →
        K2.Sem Aᵢ Aⱼ {tt} {tt} (ni (ss (hsuc hself)) u) (ni (ss (hsuc hself)) u′)
niS₂₀ Aᵢ Aⱼ hi hj hij {u} {u′} su su′ sc tt tt w w′ c c′ Y Y′ _ g g′ s cb =
  proj₁ ch ,
  (proj₂ ch ,
   (R1.ni⊑ (ss hself) (λ z z′ le → proj₁ (proj₂ (brn₀ i i h0 h0 h0 Y Y g g (Z0.sr {Y} g) z z′ le)))
                      (λ z z′ le → proj₁ (proj₂ (brn₀ j j h1 h1 h1 Y′ Y′ g′ g′ (Z0.sr {Y′} g′) z z′ le)))
                      (λ z z′ le → proj₁ (proj₂ (brn₀ i j h0 h1 hx Y Y′ g g′ s z z′ le))) ,
    R2.ni⊑ (ss (hsuc hself)) (λ z z′ le → proj₂ (proj₂ (brn₀ i i h0 h0 h0 Y Y g g (Z0.sr {Y} g) z z′ le)))
                             (λ z z′ le → proj₂ (proj₂ (brn₀ j j h1 h1 h1 Y′ Y′ g′ g′ (Z0.sr {Y′} g′) z z′ le)))
                             (λ z z′ le → proj₂ (proj₂ (brn₀ i j h0 h1 hx Y Y′ g g′ s z z′ le)))))
  where
  i = Ai₂₀ Aᵢ u w
  j = Ai₂₀ Aⱼ u′ w′
  h0 = hAi₂₀ Aᵢ Aᵢ hi hi hi {u} {u} su w w
  h1 = hAi₂₀ Aⱼ Aⱼ hj hj hj {u′} {u′} su′ w′ w′
  hx = hAi₂₀ Aᵢ Aⱼ hi hj hij {u} {u′} sc w w′
  ch = Z0.Chain.chain₀ᴳ i j h0 h1 hx Y Y′ c c′ g g′ s cb
```

## §3 `snd₂`

```agda
snd₂ : ∀ {x x′} → x ⊑₂ x′ → Sem₂ x x′
snd₂ R2.n0⊑ Aᵢ Aⱼ hi hj hij = n0S
snd₂ R2.n1⊑ Aᵢ Aⱼ hi hj hij = n1S hij
snd₂ (R2.⨾⊑ rx rx′ hx hy) Aᵢ Aⱼ hi hj hij =
  ⨾S (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ rx′ Aⱼ Aⱼ hj hj hj) (snd₂ hx Aᵢ Aⱼ hi hj hij) (K2.inn tt) (snd₂ hy Aᵢ Aⱼ hi hj hij)
snd₂ (R2.nl⊑ rd rd′ hd) Aᵢ Aⱼ hi hj hij =
  nlS (λ n → snd₂ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₂ (rd′ n) Aⱼ Aⱼ hj hj hj) (λ n → snd₂ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → K2.inn tt)
snd₂ (R2.ni⊑ (ss hself) mu mu′ cr) Aᵢ Aⱼ hi hj hij =
  niS₂₁ Aᵢ Aⱼ hi hj hij (λ z z′ le → snd₂ (mu z z′ le)) (λ z z′ le → snd₂ (mu′ z z′ le)) (λ z z′ le → snd₂ (cr z z′ le))
snd₂ (R2.ni⊑ (ss (hsuc hself)) mu mu′ cr) Aᵢ Aⱼ hi hj hij =
  niS₂₀ Aᵢ Aⱼ hi hj hij (λ z z′ le → snd₂ (mu z z′ le)) (λ z z′ le → snd₂ (mu′ z z′ le)) (λ z z′ le → snd₂ (cr z z′ le))
snd₂ (R2.nwˡ h) = snd₂ h
snd₂ (R2.nwʳ h) = snd₂ h
snd₂ (R2.nwᵉ h) = snd₂ h
snd₂ (R2.tr h h′) Aᵢ Aⱼ hi hj hij = trS (snd₂ h Aᵢ Aᵢ hi hi hi) (snd₂ h′ Aᵢ Aⱼ hi hj hij)
snd₂ (R2.u0ˡ h) Aᵢ Aⱼ hi hj hij = u0ˡS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.u0ʳ h) Aᵢ Aⱼ hi hj hij = u0ʳS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.u1ˡ h) Aᵢ Aⱼ hi hj hij = u1ˡS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.u1ʳ h) Aᵢ Aⱼ hi hj hij = u1ʳS (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.asˡ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡS (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ ry Aᵢ Aᵢ hi hi hi) (snd₂ rz Aᵢ Aᵢ hi hi hi) (K2.inn tt) (K2.inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.asˡ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡ′S (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ ry Aᵢ Aᵢ hi hi hi) (snd₂ rz Aᵢ Aᵢ hi hi hi) (K2.inn tt) (K2.inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.asʳ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳS (snd₂ rx Aⱼ Aⱼ hj hj hj) (snd₂ ry Aⱼ Aⱼ hj hj hj) (snd₂ rz Aⱼ Aⱼ hj hj hj) (K2.inn tt) (K2.inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.asʳ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳ′S (snd₂ rx Aⱼ Aⱼ hj hj hj) (snd₂ ry Aⱼ Aⱼ hj hj hj) (snd₂ rz Aⱼ Aⱼ hj hj hj) (K2.inn tt) (K2.inn tt) (snd₂ h Aᵢ Aⱼ hi hj hij)
snd₂ (R2.pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) Aᵢ Aⱼ hi hj hij =
  subst (λ t → K2.Sem Aᵢ Aⱼ {tt} {tt} (x ⨾ t) (x′ ⨾ nl d′)) (sym (preL≡ d k))
    (preS pre₃ (snd₂ rx Aᵢ Aᵢ hi hi hi) (snd₂ rx′ Aⱼ Aⱼ hj hj hj) (λ n → snd₂ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₂ (rd′ n) Aⱼ Aⱼ hj hj hj)
          (snd₂ hx Aᵢ Aⱼ hi hj hij) (K2.inn tt) (λ n → snd₂ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → K2.inn tt) k)
```
