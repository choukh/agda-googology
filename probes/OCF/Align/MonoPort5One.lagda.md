# 第三站 (四): 实例 3 的第 1 层语义

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 实例 3, 观测 `O₃`. 第 0 层用 [MonoPort4Zero](MonoPort4Zero.lagda.md) 的 `snd₀ᴳ`, `chain₀ᴳ` (实例取 3, 观测取 `O₃`). 第 1 层用核 [MonoPort3Gen](MonoPort3Gen.lagda.md):
>
> - 上下文关系 `Cx₁`: $\sqsubseteq_1$, 两边沿 ⨾ 左脊自比 (`Ok`). 第 1 层的上下文被第 2 层节点的 `Ai` 当坐标读, 所以要 $\sqsubseteq_1$; 部分和那条上下文律要拆出前缀的自比, 所以要 `Ok` 而不只是自比.
> - **节点一步** (`niS₁`, 第 1 层节点, 坐标在第 0 层): $T_0$ 上上升, 由 `chain₀ᴳ`; $T_1$, $T_2$ 上保留, 分支 `BNi` 是 "先在第 0 层走坐标、再在第 1 层走分支", 由 `snd₀ᴳ` 与分支的语义给 (`brn₀`, 对一切第 0 层动作写一次). 动作 `Ai` 满足 `HA` (`hAi₁`): 分支的上下文是 `nw w ⨾ Int z`, 由 [MonoPort5Int](MonoPort5Int.lagda.md) 的 `IntM`.
> - **`snd₁`**: $x\sqsubseteq_1x'$ ⇒ 两动作的第 1 层语义, 对 $\sqsubseteq_1$ 的推导归纳; 和的构造子全由核, `nw` 三条各一行.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
module OCF.Align.MonoPort5One {W : A} (lW : Lg W) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.HtFeedTree using (D; hz; hs; hself; hsuc; ss; accL; n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.MonoPort5Rel lW
open import OCF.Align.MonoPort5Int lW
import OCF.Align.MonoPort4Zero as Z
import OCF.Align.MonoPort5Chn as Chn

module Z0 = Z.R0 Λ₃ tt lW k0 O₃ pre₃ proj₁

ac₁ = accL L1

Cx₁ In₁ : D L1 W → D L1 W → Set
Cx₁ w w′ = (w ⊑₁ w′) × (R1.Ok w × R1.Ok w′)
In₁ x x′ = (x ⊑₁ x′) × (Rf₁ x × Rf₁ x′)

module C1 = Chn Λ₃ tt lW k0 O₃ L1 ac₁ k1 Cx₁ In₁
module K1 = C1.K

preL≡ : ∀ {ly V} (d : ℕ → D ly V) k → preL d k ≡ G.preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)
```

## §1 上下文律

```agda
cl₁ : K1.CxLaws
cl₁ = record
  { cxL = λ { (K1.cx (_ , (o , _))) → K1.cx (R1.OkRf o , (o , o)) }
  ; cxR = λ { (K1.cx (_ , (_ , o′))) → K1.cx (R1.OkRf o′ , (o′ , o′)) }
  ; cx⨾ = λ { _ _ (K1.cx (hw , (o , o′))) (K1.inn (hx , (rx , rx′))) →
              K1.cx (R1.⨾⊑ (R1.OkRf o) (R1.OkRf o′) hw (R1.nwˡ (R1.nwʳ hx)) , ((o , R1.rnw rx) , (o′ , R1.rnw rx′))) }
  ; cx0ˡ = λ { _ (K1.cx (hw , (o , o′))) →
               K1.cx (R1.tr (R1.⨾⊑ (R1.OkRf o) (R1.OkRf o) (R1.OkRf o) (R1.nwˡ R1.n0⊑)) (R1.u1ˡ hw) , ((o , R1.rnw R1.n0⊑) , o′)) }
  ; cx0ʳ = λ { _ (K1.cx (hw , (o , o′))) →
               K1.cx (R1.tr (R1.u1ʳ hw) (R1.⨾⊑ (R1.OkRf o′) (R1.OkRf o′) (R1.OkRf o′) R1.n0⊑) , (o , (o′ , R1.rnw R1.n0⊑))) }
  ; cxas = λ { _ (K1.cx (_ , (o , _))) (K1.inn (_ , (rx , _))) (K1.inn (_ , (ry , _))) →
               K1.cx (R1.asʳ′ (R1.OkRf o) (R1.rnw rx) (R1.rnw ry) (R1.⨾⊑ (R1.OkRf o) (R1.OkRf o) (R1.OkRf o) (R1.nwd rx ry)) ,
                      ((o , R1.rnw (R1.⨾⊑ rx rx rx ry)) , ((o , R1.rnw rx) , R1.rnw ry))) }
  ; cxas′ = λ { _ (K1.cx (_ , (o , _))) (K1.inn (_ , (rx , _))) (K1.inn (_ , (ry , _))) →
                K1.cx (R1.asˡ (R1.OkRf o) (R1.rnw rx) (R1.rnw ry) (R1.⨾⊑ (R1.OkRf o) (R1.OkRf o) (R1.OkRf o) (R1.nwd′ rx ry)) ,
                       (((o , R1.rnw rx) , R1.rnw ry) , (o , R1.rnw (R1.⨾⊑ rx rx rx ry)))) }
  ; cxpre = λ { {d = d} _ _ n (K1.cx (h , ((o , rP) , oR))) (K1.inn (he , (rd , re))) →
                let rP′ = R1.nwᵉ rP
                    rw = R1.OkRf o
                    rwP = R1.⨾⊑ rw rw rw rP
                in K1.cx (R1.tr (R1.asʳ′ rw rP (R1.rnw rd) (R1.⨾⊑ rw rw rw (R1.nwd rP′ rd)))
                                (R1.⨾⊑ rwP (R1.OkRf oR) h (R1.nwˡ (R1.nwʳ he))) ,
                          ((o , R1.rnw (R1.⨾⊑ rP′ rP′ rP′ rd)) , (oR , R1.rnw re))) }
  ; cxlim = λ { {d = d} _ n (K1.cx (h , (oL , (o , rP)))) (K1.inn (_ , (rd , _))) →
                let rP′ = R1.nwᵉ rP
                    rw = R1.OkRf o
                    rwP = R1.⨾⊑ rw rw rw rP
                in K1.cx (R1.tr (R1.⨾⊑ (R1.OkRf oL) rwP h (R1.rnw rd))
                                (R1.asˡ rw rP (R1.rnw rd) (R1.⨾⊑ rw rw rw (R1.nwd′ rP′ rd))) ,
                          ((oL , R1.rnw rd) , (o , R1.rnw (R1.⨾⊑ rP′ rP′ rP′ rd)))) }
  }

open K1.Steps cl₁
```

## §2 第 0 层节点的分支, 对一切第 0 层动作

`BNi` 在 `self` 上的值: 状态先加上坐标 $z$ 在第 0 层的输出 (动作 $i$, 上下文 `n0`), 再在这个状态上用 $i$ 读 $z$. 后一步正是 $i$ 的 `HA`.

```agda
Sv : Z0.Act → P.St W → D hz W → P.St W
Sv i Y z = P.cv C.self Y G.⊕ Z0.Run (P.Ig↾ C.self i) z C.self n0 (P.cv C.self Y)

brn₀ : ∀ (i j : Z0.Act) → Z0.HA i i → Z0.HA j j → Z0.HA i j → ∀ (Y Y′ : P.St W) → Z0.Good Y → Z0.Good Y′ → Z0.SRel Y Y′ →
       ∀ (z z′ : D hz W) → z ⊑₀ z′ → i C.self lW z (Sv i Y z) ≼ j C.self lW z′ (Sv j Y′ z′)
brn₀ i j hi hj hij Y Y′ g g′ s z z′ le = proj₂ (hij z z′ azero azero S S′ (Z0.cx le) gS gS′ sS z≤)
  where
  i′ = P.Ig↾ C.self i
  j′ = P.Ig↾ C.self j
  Y₁ = P.cv C.self Y
  Y₁′ = P.cv C.self Y′
  Δ = Z0.Run i′ z C.self n0 Y₁
  Δ′ = Z0.Run j′ z′ C.self n0 Y₁′
  S = Y₁ G.⊕ Δ
  S′ = Y₁′ G.⊕ Δ′
  o = Z0.snd₀ᴳ le i′ j′ hi hj hij C.self C.self n0 n0 (G.vY Y) (G.vY Y′) Y₁ Y₁′ (Z0.cx z0) g g′ s (proj₁ s)
  rΔ = proj₂ (Z0.snd₀ᴳ (refl₀ z) i′ i′ hi hi hi C.self C.self n0 n0 azero azero Y₁ Y₁ (Z0.cx z0) g g (Z0.sr {Y₁} g) z≤)
  rΔ′ = proj₂ (Z0.snd₀ᴳ (refl₀ z′) j′ j′ hj hj hj C.self C.self n0 n0 azero azero Y₁′ Y₁′ (Z0.cx z0) g′ g′ (Z0.sr {Y₁′} g′) z≤)
  gS = Z0.G⊕ {Y₁} {Δ} g rΔ
  gS′ = Z0.G⊕ {Y₁′} {Δ′} g′ rΔ′
  sS = Z0.S⊕ {Y₁} {Y₁′} {Δ} {Δ′} g g′ s o
```

## §3 第 1 层节点一步

```agda
Sem₁ : D L1 W → D L1 W → Set
Sem₁ x x′ = ∀ (Aᵢ Aⱼ : K1.Act) → K1.HA Aᵢ Aᵢ → K1.HA Aⱼ Aⱼ → K1.HA Aᵢ Aⱼ → K1.Sem Aᵢ Aⱼ {tt} {tt} x x′

Ai₁₀ : K1.Act → U₁ → D L1 W → Z0.Act
Ai₁₀ A₀ u w = P.Ai ac₁ (accL hz) (ss hself) u C.self k0 k1 A₀ w

Uf : U₁ → U₁
Uf u p′ l′ z′ = u (C.⊲-tr C.self p′) l′ z′

hAi₁ : ∀ (Aᵢ Aⱼ : K1.Act) → K1.HA Aᵢ Aᵢ → K1.HA Aⱼ Aⱼ → K1.HA Aᵢ Aⱼ → ∀ {u u′ : U₁} → Mo u u → Mo u′ u′ → Mo u u′ →
       (∀ z z′ → z ⊑₀ z′ → Sem₁ (u C.self lW z) (u′ C.self lW z′)) → ∀ {w w′} → Cx₁ w w′ → Z0.HA (Ai₁₀ Aᵢ u w) (Ai₁₀ Aⱼ u′ w′)
hAi₁ Aᵢ Aⱼ hi hj hij {u} {u′} mu mu′ cr sc {w} {w′} (hw , (ow , ow′)) z z′ c c′ Y Y′ (Z0.cx le) g g′ s cb =
  sc z z′ le (P.Ig↾ C.self Aᵢ) (P.Ig↾ C.self Aⱼ) hi hj hij tt tt _ _ c c′ Y Y′ (K1.cx ctx) g g′ s cb
  where
  rw = R1.OkRf ow
  rw′ = R1.OkRf ow′
  ctx = R1.⨾⊑ (R1.rnw rw) (R1.rnw rw′) (R1.nwˡ (R1.nwʳ hw)) (IntM {u = Uf u} {u′ = Uf u′} mu mu′ cr le C.self C.self z0) ,
        ((R1.rnw rw , IntR {u = Uf u} mu z C.self n0) , (R1.rnw rw′ , IntR {u = Uf u′} mu′ z′ C.self n0))

niS₁ : ∀ (Aᵢ Aⱼ : K1.Act) (hi : K1.HA Aᵢ Aᵢ) (hj : K1.HA Aⱼ Aⱼ) (hij : K1.HA Aᵢ Aⱼ) {u u′ : U₁} → Mo u u → Mo u′ u′ → Mo u u′ →
       (∀ z z′ → z ⊑₀ z′ → Sem₁ (u C.self lW z) (u C.self lW z′)) → (∀ z z′ → z ⊑₀ z′ → Sem₁ (u′ C.self lW z) (u′ C.self lW z′)) →
       (∀ z z′ → z ⊑₀ z′ → Sem₁ (u C.self lW z) (u′ C.self lW z′)) → K1.Sem Aᵢ Aⱼ {tt} {tt} (ni (ss hself) u) (ni (ss hself) u′)
niS₁ Aᵢ Aⱼ hi hj hij {u} {u′} mu mu′ cr su su′ sc tt tt w w′ c c′ Y Y′ (K1.cx cw) g g′ s cb =
  proj₁ ch ,
  (proj₂ ch ,
   (R1.ni⊑ (ss hself) (λ z z′ le → proj₁ (proj₂ (brn₀ i i h0 h0 h0 Y Y g g (Z0.sr {Y} g) z z′ le)))
                      (λ z z′ le → proj₁ (proj₂ (brn₀ j j h1 h1 h1 Y′ Y′ g′ g′ (Z0.sr {Y′} g′) z z′ le)))
                      (λ z z′ le → proj₁ (proj₂ (brn₀ i j h0 h1 hx Y Y′ g g′ s z z′ le))) ,
    R2.ni⊑ (ss (hsuc hself)) (λ z z′ le → proj₂ (proj₂ (brn₀ i i h0 h0 h0 Y Y g g (Z0.sr {Y} g) z z′ le)))
                             (λ z z′ le → proj₂ (proj₂ (brn₀ j j h1 h1 h1 Y′ Y′ g′ g′ (Z0.sr {Y′} g′) z z′ le)))
                             (λ z z′ le → proj₂ (proj₂ (brn₀ i j h0 h1 hx Y Y′ g g′ s z z′ le)))))
  where
  i = Ai₁₀ Aᵢ u w
  j = Ai₁₀ Aⱼ u′ w′
  o = proj₁ (proj₂ cw)
  o′ = proj₂ (proj₂ cw)
  h0 = hAi₁ Aᵢ Aᵢ hi hi hi {u} {u} mu mu mu su (R1.OkRf o , (o , o))
  h1 = hAi₁ Aⱼ Aⱼ hj hj hj {u′} {u′} mu′ mu′ mu′ su′ (R1.OkRf o′ , (o′ , o′))
  hx = hAi₁ Aᵢ Aⱼ hi hj hij {u} {u′} mu mu′ cr sc cw
  ch = Z0.Chain.chain₀ᴳ i j h0 h1 hx Y Y′ c c′ g g′ s cb
```

## §4 `snd₁`

```agda
snd₁ : ∀ {x x′} → x ⊑₁ x′ → Sem₁ x x′
snd₁ R1.n0⊑ Aᵢ Aⱼ hi hj hij = n0S
snd₁ R1.n1⊑ Aᵢ Aⱼ hi hj hij = n1S hij
snd₁ (R1.⨾⊑ rx rx′ hx hy) Aᵢ Aⱼ hi hj hij =
  ⨾S (snd₁ rx Aᵢ Aᵢ hi hi hi) (snd₁ rx′ Aⱼ Aⱼ hj hj hj) (snd₁ hx Aᵢ Aⱼ hi hj hij) (K1.inn (hx , (rx , rx′))) (snd₁ hy Aᵢ Aⱼ hi hj hij)
snd₁ (R1.nl⊑ rd rd′ hd) Aᵢ Aⱼ hi hj hij =
  nlS (λ n → snd₁ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₁ (rd′ n) Aⱼ Aⱼ hj hj hj) (λ n → snd₁ (hd n) Aᵢ Aⱼ hi hj hij)
      (λ n → K1.inn (hd n , (rd n , rd′ n)))
snd₁ (R1.ni⊑ (ss hself) mu mu′ cr) Aᵢ Aⱼ hi hj hij =
  niS₁ Aᵢ Aⱼ hi hj hij mu mu′ cr (λ z z′ le → snd₁ (mu z z′ le)) (λ z z′ le → snd₁ (mu′ z z′ le)) (λ z z′ le → snd₁ (cr z z′ le))
snd₁ (R1.nwˡ h) = snd₁ h
snd₁ (R1.nwʳ h) = snd₁ h
snd₁ (R1.nwᵉ h) = snd₁ h
snd₁ (R1.tr h h′) Aᵢ Aⱼ hi hj hij = trS (snd₁ h Aᵢ Aᵢ hi hi hi) (snd₁ h′ Aᵢ Aⱼ hi hj hij)
snd₁ (R1.u0ˡ h) Aᵢ Aⱼ hi hj hij = u0ˡS (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.u0ʳ h) Aᵢ Aⱼ hi hj hij = u0ʳS (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.u1ˡ h) Aᵢ Aⱼ hi hj hij = u1ˡS (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.u1ʳ h) Aᵢ Aⱼ hi hj hij = u1ʳS (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.asˡ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡS (snd₁ rx Aᵢ Aᵢ hi hi hi) (snd₁ ry Aᵢ Aᵢ hi hi hi) (snd₁ rz Aᵢ Aᵢ hi hi hi) (K1.inn (rx , (rx , rx))) (K1.inn (ry , (ry , ry)))
       (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.asˡ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asˡ′S (snd₁ rx Aᵢ Aᵢ hi hi hi) (snd₁ ry Aᵢ Aᵢ hi hi hi) (snd₁ rz Aᵢ Aᵢ hi hi hi) (K1.inn (rx , (rx , rx))) (K1.inn (ry , (ry , ry)))
        (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.asʳ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳS (snd₁ rx Aⱼ Aⱼ hj hj hj) (snd₁ ry Aⱼ Aⱼ hj hj hj) (snd₁ rz Aⱼ Aⱼ hj hj hj) (K1.inn (rx , (rx , rx))) (K1.inn (ry , (ry , ry)))
       (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.asʳ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  asʳ′S (snd₁ rx Aⱼ Aⱼ hj hj hj) (snd₁ ry Aⱼ Aⱼ hj hj hj) (snd₁ rz Aⱼ Aⱼ hj hj hj) (K1.inn (rx , (rx , rx))) (K1.inn (ry , (ry , ry)))
        (snd₁ h Aᵢ Aⱼ hi hj hij)
snd₁ (R1.pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) Aᵢ Aⱼ hi hj hij =
  subst (λ t → K1.Sem Aᵢ Aⱼ {tt} {tt} (x ⨾ t) (x′ ⨾ nl d′)) (sym (preL≡ d k))
    (preS pre₃ (snd₁ rx Aᵢ Aᵢ hi hi hi) (snd₁ rx′ Aⱼ Aⱼ hj hj hj) (λ n → snd₁ (rd n) Aᵢ Aᵢ hi hi hi) (λ n → snd₁ (rd′ n) Aⱼ Aⱼ hj hj hj)
          (snd₁ hx Aᵢ Aⱼ hi hj hij) (K1.inn (hx , (rx , rx′))) (λ n → snd₁ (hd n) Aᵢ Aⱼ hi hj hij) (λ n → K1.inn (hd n , (rd n , rd′ n))) k)
```
