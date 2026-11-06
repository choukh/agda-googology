# NegValX (六): 对构造一路 ValX 的定理的检查: 严格档, 前提, 同分量同层, UIP

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 对构造一路 ValX 已交的文件 (`ValXRel`, `ValXObs`, `ValXGoal`, `ValXTm`; 只导入, 不改) 与接口 [ValXIf](ValXIf.lagda.md) §5 `ValX⁻`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP 与函数外延 (连前提也没有; 只导入 ValX 里不带 UIP 参数的模块).
>
> **四个问题 (主审续派).**
>
> 1. **严格是否只是 "多一个后继" 档.** 是. `TU2-above` 的陈述形状对**任何**输出 $\ge1$ 的族的对角都成立 (`Diag.above₊`, 定理); 取常值 $1$ 的族, 对角的值 $\le\omega$ (`blind-ω`, 定理). 所以 `TU2-above` 不区分 `TU2` 与 $\omega$. `goal-if` 的 $+1$ 同样只来自 `TU 1` 的第二个部分和 $\ge1$ (`oneX`; 读 `ValXGoal.goal-if′` 的证明, 判断).
> 2. **前提是否可满足.** (a) `monoX` 的前提 `MoX` 有实例 (ValX 的 `MoX-gt`, `MoX-Ω₁`; 本篇 `MoX-Xn`, `MoX-Yn`, `MoX-C₁`, `MoX-C₂`). (b) **`TU 1` 的回灌链第 0 点不值合法** (`¬MoX-u₀`, 定理), 所以 **`¬MoX-inU₁`** (定理): 接口 §3 `ValXU₁` 的字段 `U₁-Mo` 对 ValX 的 `MoX` 不能满足. (c) **P2 与 floor-block.** `P2` 未否定. 但经任一 "层反射" 关系证 `P2` 在 $b_1=1+\omega_1\le b_2=1+\omega_2$ 处被挡: `kR` 在 $b_i$ 处折的输入是 $g_0(\mathrm{sh}_0\,W_0\,b_i)$, 对一切层反射的 $R$, $\neg R(g_0(\mathrm{sh}_0 W_0 b_1), g_0(\mathrm{sh}_0 W_0 b_2))$ (`P2-block`, 定理). 这是 `floor-block` 搬到 `kR` 实际读的坐标上 (回灌之后) 与 `U` 之后 (`InvU`: 嵌入再折回不出新分量).
> 3. **"同分量同层" 的 `Ω≤Ω`.** 不撞 `self≰copy`: $\Omega_1$ 本身 (分量 $0$) 与拷贝 (分量 $1$) 不可比 (`self-unrel`), 两者都值合法 (`MoX-Xn`, `MoX-Yn`). 仍对 `copies-same` 盲: 分量 $1$, $2$ 里的两个拷贝都值合法, 互不可比 (`copies-unrel`), 跨底折叠后字面相等 (`copies-blind`). 另有对 `ValX⁻` 的 `self≤copy-excl⁻` (同前, 换成 `ValX⁻`).
> 4. **UIP 条件是否必要.** 不全必要: `kcC` 用到的是第 $0$ 层的 K, 无条件可证 (`K-hz`). 更一般, 一切**有限**层号上 K 与 "自环只有 `hself`" 无条件成立 (`K-fin`, `loop-fin`); 所以 ValC 的 `sameR` 只在**带 ℕ-极限**的层号上需要前提. 在那里它等价于该层的 K (`NegValXUip.loop→K` 与本篇 `K→loop`), 并推出函数类型上的 K (`KAt→Kfun`). 判断: 跨底的闭项要用到带极限的层号 (`gt C`, $C$ 无穷), 所以这一部分没有去掉; UIP 对值定理是否必要没有证明 (元定理).
>
> **前提实例.** `Diag`: 族 `TU` 本身 (ValX 的 `one≤TU`), 常值族 (`blind-ω`). `P2-block` 的 $R$: ValX 的 `_≤X_` (`refl≤X`). 世界、路径: 同 `NegValXSelf`, `NegValXCopy`.
>
> **只否定什么.** `¬MoX-u₀`, `¬MoX-inU₁`: 只否定 ValX 的 `MoX` 覆盖 `TU 1` 的输入 (`ValXU₁` 的字段 `U₁-Mo`); 不否定 `TX + 1 ≤ TU 1`. `P2-block`: 只否定经层反射关系 (含 `_≤X_`) 与跨底单调证 `P2`; **不否定 `P2`**, 也不否定跨层的关系 (ValX 接手清单 (a)) 或直接在第 0 层证 (b). `self-unrel`, `copies-unrel`: 关于 `_≤X_` 的事实, 不是对 ValX 的否定. `K-fin`, `loop-fin`: 正面结果, 缩小 UIP 前提起作用的范围.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf using (CRwIf)
open import OCF.Lean.CRw using (I₁; W₀; leg; Σ₀)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁ using (LeAt; MoAt; module Rel; module L; nos; nl; ppl)
open import OCF.Lean.ValCUip using (Code; rc; encode)
open import OCF.Lean.ValXRel I₁ using (HX; _≤X_; MoX; ≤X-refl; z≤; ≤s; ≤Ω)
open import OCF.Lean.ValXObs I₁ using (HasL; LvRefl; Inv; Inv-⊞; Inv-gt; has-inv; refl≤X; not⊲; le₁₂; ω₁; ω₂; moAll; nat)
open import OCF.Lean.ValXGoal using (g₀)
open import OCF.Lean.ValXIf I₁ using (inU₁; ValX⁻; FX)
open import OCF.Lean.NegValXSelf using (Xn; Yn; g; Big; g-cases; g-up; κc; F; module Self)
open import OCF.Lean.NegValXCopy using (κc₂; copies-same)
open import OCF.Lean.NegValXUip using (KAt; SelfLoopAt; KAt→Kfun)
```

## §1 严格档: 对角的 "+1" 对一切输出 $\ge1$ 的族成立

```agda
module Diag (Fm : (m : Cd) → LgB m → Cd) (lgF : ∀ m l → LgB (Fm m l)) where
  y : ℕ → Cd
  lg-y : ∀ n → LgB (y n)
  y zero = hz
  y (suc n) = y n ⊞ Fm (hs (y n)) (lg-y n)
  lg-y zero = tt
  lg-y (suc n) = Lg-⊞ (y n) (Fm (hs (y n)) (lg-y n)) (lg-y n) (lgF _ _)

  D : Cd
  D = hl y

  -- 同 ValXTm.TU2-above 的证明, 只用 "族的输出 ≥ 1"
  above₊ : (∀ m l → LeAt hz (hs hz) (Fm m l)) → ∀ n → LeAt hz (hs (Fm (hs (y n)) (lg-y n))) D
  above₊ one n =
    Rel.≤l (suc (suc n))
      (L.≤-trans hz (Rel.s≤s (L.≤⊞ˡ hz (y n) (Fm (hs (y n)) (lg-y n))))
                    (L.⊞-monoʳ hz (y (suc n)) (one (hs (y (suc n))) (lg-y (suc n)))))

-- 常值族 1: 对角的值 ≤ ω, 而 "+1" 的形状照样成立
module D1 = Diag (λ _ _ → hs hz) (λ _ _ → tt)

y≡nat : ∀ n → D1.y n ≡ nat n
y≡nat zero = refl
y≡nat (suc n) = cong hs (y≡nat n)

blind-ω : (∀ n → LeAt hz (hs (hs hz)) D1.D) × LeAt hz D1.D ω₁
blind-ω = D1.above₊ (λ _ _ → L.≤-refl hz (hs hz)) ,
          Rel.l≤l (λ n → n) (L.idInc hz) (λ n → subst (λ z → LeAt hz z (nat n)) (sym (y≡nat n)) (L.≤-refl hz (nat n)))
```

## §2 `TU 1` 的输入不值合法; P2 经层反射关系被挡

**嵌入再折回不出新分量** (`InvU`): $U\,b\,x=\Phi_{\Omega_1\oplus1\to\Omega_1,b}(\mathrm{up}\,x)$ 只留下 `XS` 的种类 (底种类一律留, 定义上的等式), 所以保 `ValXObs.Inv`.

```agda
Inv-mul : ∀ {W} a → Inv W a → ∀ n → Inv W (mul a n)
Inv-mul a v zero = v
Inv-mul a v (suc n) = Inv-⊞ (mul a n) a (Inv-mul a v n) v

Inv-Σ : ∀ {W} (f : ℕ → HX) → (∀ n → Inv W (f n)) → ∀ n → Inv W (Σ⁺ f n)
Inv-Σ f v zero = v 0
Inv-Σ f v (suc n) = Inv-⊞ (Σ⁺ f n) (f (suc n)) (Inv-Σ f v n) (v (suc n))

InvU : ∀ {W} rs (b : HX) (x : HX) → Inv W x →
       Inv W (Φ bX (hs hz) (acc rs) tt bX hz (sm (hsuc hself)) b (up x) tt)
InvU rs b hz v = tt
InvU rs b (hs x) v = Inv-mul _ (InvU rs b x v)
InvU rs b (hl f) v = Inv-Σ _ (λ n → InvU rs b (f n) (v n))
InvU rs b (hΩ (c , κ) h) (q , v) = q , λ e → InvU rs b (h e) (v e)

-- g₀ (c+1) 的根是第 c 层的种类 (c , Ω_{c+1}); 右边的一切种类在 c′+1 之下
blockU : ∀ (R : HX → HX → Set) → LvRefl R → ∀ c₁ c₂ → ¬ (hs c₁ ⊲ hs c₂) → ¬ R (g₀ (hs c₁)) (g₀ (hs c₂))
blockU R rf c₁ c₂ n r = n (has-inv (rf r) (InvU _ topL (gt (hs c₂)) (Inv-gt (hs c₂) hself)))
```

**`TU 1` 的回灌链第 0 点** $u_0=\Omega_1(g_0)$ (`ValXGoal.u₀≡`) 不值合法; 于是 `inU₁` 不值合法.

```agda
κΩ : K XS
κΩ = hz , inj₂ tt

¬MoX-u₀ : ¬ MoX (hΩ κΩ g₀)
¬MoX-u₀ (mo , _) = blockU _≤X_ refl≤X ω₁ ω₂ not⊲ (mo (hs ω₁) (hs ω₂) (moAll (hs ω₁)) (moAll (hs ω₂)) le₁₂)

¬MoX-inU₁ : ¬ MoX inU₁
¬MoX-inU₁ m = ¬MoX-u₀ (m 0)
```

**P2 在回灌之后的坐标上被挡.** `kR b` 折的是 $g_0(\mathrm{sh}_0\,W_0\,b)$ (`ValXGoal.kR`, 坐标经 `psh` 回灌). 取 $b_1=1+\omega_1\le b_2=1+\omega_2$: 回灌后的两个坐标是 $c_i'+1$, $c_i'=1\boxplus\mathrm{leg}\,\omega_i$, 两者值相同而结构不同 ($c_2'$ 的基本列是 $c_1'$ 的去掉首项), $c_1'+1\not\lhd c_2'+1$.

```agda
NoLim : Cd → Set
NoLim hz = ⊤
NoLim (hs x) = NoLim x
NoLim (hl _) = ⊥
NoLim (hΩ () _)

nl⊲ : ∀ {a b : Cd} → a ⊲ b → NoLim b → NoLim a
nl⊲ hself v = v
nl⊲ (hsuc q) v = nl⊲ q v
nl⊲ (hlim n q) ()
nl⊲ (hLim {κ = ()} _ _) v

NoLim-⊞ : ∀ a b → NoLim a → NoLim b → NoLim (a ⊞ b)
NoLim-⊞ a hz va vb = va
NoLim-⊞ a (hs b) va vb = NoLim-⊞ a b va vb
NoLim-⊞ a (hl f) va ()
NoLim-⊞ a (hΩ () _) va vb

NoLim-leg : ∀ k → NoLim (leg (nat k))
NoLim-leg zero = tt
NoLim-leg (suc k) = NoLim-leg k

NoLim-Σ₀ : ∀ (f : ℕ → Cd) → (∀ k → NoLim (f k)) → ∀ n → NoLim (Σ₀ f n)
NoLim-Σ₀ f v zero = v 0
NoLim-Σ₀ f v (suc n) = NoLim-⊞ (Σ₀ f n) (f (suc n)) (NoLim-Σ₀ f v n) (v (suc n))

not⊲g : ∀ {f₁ f₂ : ℕ → Cd} → (∀ n → NoLim (f₂ n)) → ¬ (hl f₁ ≡ hl f₂) → ¬ (hs (hl f₁) ⊲ hs (hl f₂))
not⊲g v ne hself = ne refl
not⊲g v ne (hsuc (hlim n q)) = nl⊲ q (v n)

sh : Cd → Cd → Cd
sh = CRwIf.sh₀ I₁

c₁′ c₂′ : Cd
c₁′ = W₀ ⊞ leg ω₁
c₂′ = W₀ ⊞ leg ω₂

sh₁≡ : sh W₀ (hs ω₁) ≡ hs c₁′
sh₁≡ = refl

sh₂≡ : sh W₀ (hs ω₂) ≡ hs c₂′
sh₂≡ = refl

private
  at0 : Cd → Cd
  at0 (hl f) = f 0
  at0 _ = hz
  isZ1 : Cd → Set
  isZ1 (hs hz) = ⊤
  isZ1 _ = ⊥

c′-ne : ¬ (c₁′ ≡ c₂′)
c′-ne e = subst isZ1 (cong at0 e) tt

not⊲′ : ¬ (hs c₁′ ⊲ hs c₂′)
not⊲′ = not⊲g (λ n → NoLim-⊞ W₀ _ tt (NoLim-Σ₀ (λ k → leg (nat (suc k))) (λ k → NoLim-leg (suc k)) n)) c′-ne

P2-block : ∀ (R : HX → HX → Set) → LvRefl R →
           LeAt hz (hs ω₁) (hs ω₂) × ¬ R (g₀ (sh W₀ (hs ω₁))) (g₀ (sh W₀ (hs ω₂)))
P2-block R rf = le₁₂ , blockU R rf c₁′ c₂′ not⊲′

-- 实例: ValX 自己的关系
P2-block-≤X : ¬ (g₀ (sh W₀ (hs ω₁)) ≤X g₀ (sh W₀ (hs ω₂)))
P2-block-≤X = proj₂ (P2-block _≤X_ refl≤X)
```

## §3 同分量同层的 `Ω≤Ω`: 本身与拷贝不可比; 两个拷贝仍盲

```agda
noΩ≤0 : ∀ {κ h} → ¬ (hΩ κ h ≤X hz)
noΩ≤0 ()

noΩ≤1 : ∀ {κ h} → ¬ (hΩ κ h ≤X hs hz)
noΩ≤1 (≤s p) = noΩ≤0 p

noΩ≤2 : ∀ {κ h} → ¬ (hΩ κ h ≤X Big)
noΩ≤2 (≤s p) = noΩ≤1 p

noΩ≤g : ∀ {κ h} c → ¬ (hΩ κ h ≤X g c)
noΩ≤g {κ} {h} c p with g-cases c
... | inj₁ e = noΩ≤0 (subst (λ z → hΩ κ h ≤X z) e p)
... | inj₂ e = noΩ≤2 (subst (λ z → hΩ κ h ≤X z) e p)

mo-g : ∀ c c′ → LeAt hz c c′ → g c ≤X g c′
mo-g c c′ p with g-cases c
... | inj₁ e = subst (λ z → z ≤X g c′) (sym e) z≤
... | inj₂ e = subst₂ _≤X_ (sym e) (sym (g-up p e)) (≤X-refl Big)

MoX-g : ∀ c → MoX (g c)
MoX-g hz = tt
MoX-g (hs c) = MoX-g c
MoX-g (hl f) = tt
MoX-g (hΩ () _)

MoX-Xn : MoX Xn
MoX-Xn = (λ c c′ _ _ p → mo-g c c′ p) , (λ c _ → MoX-g c)

MoX-Yn : MoX Yn
MoX-Yn = (λ c c′ _ _ p → mo-g c c′ p) , (λ c _ → MoX-g c)

self-unrel : ¬ (Xn ≤X Yn)
self-unrel (≤Ω c _ _ p) = noΩ≤g c p
```

两个拷贝 (分量 $1$, $2$), 分支恒为 $0$.

```agda
h0 : Cd → HX
h0 _ = hz

C₁ C₂ : HX
C₁ = hΩ κc h0
C₂ = hΩ κc₂ h0

MoX-C₁ : MoX C₁
MoX-C₁ = (λ _ _ _ _ _ → z≤) , (λ _ _ → tt)

MoX-C₂ : MoX C₂
MoX-C₂ = (λ _ _ _ _ _ → z≤) , (λ _ _ → tt)

copies-unrel : ¬ (C₁ ≤X C₂) × ¬ (C₂ ≤X C₁)
copies-unrel = (λ { (≤Ω c _ _ p) → noΩ≤0 p }) , (λ { (≤Ω c _ _ p) → noΩ≤0 p })

copies-blind : ∀ (B : Cd) (lB : LgB B) (pt : hz ⊲ B) (b : Cd) (ev₁ : hs (hs hz) ⊲ B) (ev₂ : hs (hs (hs hz)) ⊲ B) →
               F B lB pt b C₁ (ev₁ , λ _ _ → tt) ≡ F B lB pt b C₂ (ev₂ , λ _ _ → tt)
copies-blind B lB pt b = copies-same B lB pt b h0 (λ _ _ → tt)
```

**对 `ValX⁻`** (接口 §5): 同 `NegValXIfSelf`, 锚不同, 证明不用锚.

```agda
module OnX⁻ (X : ValX⁻) (B : Cd) (lB : LgB B) (e2 : hs (hs hz) ⊲ B) (gB : g B ≡ Big) (pt : hz ⊲ B) where
  module V⁻ = ValX⁻ X
  open Self B lB e2 gB

  self≤copy-excl⁻ : V⁻.MoX Xn → V⁻.MoX Yn → ¬ V⁻.LeX Xn Yn
  self≤copy-excl⁻ mx my p =
    self≰copy pt (V⁻.sound₀ (V⁻.X-mono B lB hz pt pt ndX ndY
      (V⁻.Mo-hz hz) (V⁻.Mo-hz hz) (V⁻.le-refl hz hz) (V⁻.le-refl hz hz) mx my p))
```

## §4 UIP: 有限层号上无条件; 只在带极限的层号上起作用

**有限树上的 K** (编码-解码, 不用函数外延: 有限树没有 ℕ-极限).

```agda
decF : ∀ x y → NoLim x → Code x y → x ≡ y
decF hz hz _ _ = refl
decF (hs x) (hs y) v c = cong hs (decF x y v c)
decF hz (hs _) _ ()
decF hz (hl _) _ ()
decF hz (hΩ () _) _ _
decF (hs _) hz _ ()
decF (hs _) (hl _) _ ()
decF (hs _) (hΩ () _) _ _
decF (hl _) _ () _
decF (hΩ () _) _ _ _

decF-rc : ∀ x (v : NoLim x) → decF x x v (rc x) ≡ refl
decF-rc hz v = refl
decF-rc (hs x) v = cong (cong hs) (decF-rc x v)
decF-rc (hl _) ()
decF-rc (hΩ () _) v

dec-enc : ∀ {x y} (v : NoLim x) (e : x ≡ y) → decF x y v (encode e) ≡ e
dec-enc {x} v refl = decF-rc x v

codeP : ∀ x → NoLim x → (c c′ : Code x x) → c ≡ c′
codeP hz v c c′ = refl
codeP (hs x) v c c′ = codeP x v c c′
codeP (hl _) ()
codeP (hΩ () _) v

K-fin : ∀ {x} → NoLim x → KAt x
K-fin {x} v e = trans (sym (dec-enc v e)) (trans (cong (decF x x v) (codeP x v (encode e) (rc x))) (dec-enc v refl))

-- ValXMono.kcC 的分量 0 用到的正是这一条
K-hz : ∀ (e : hz ≡ hz) → e ≡ refl
K-hz = K-fin tt
```

**K ⟹ 自环只有 `hself`** (逐层号; 与 `NegValXUip.loop→K` 合成逐层号的等价).

```agda
Kmove : ∀ {k a : Cd} → KAt k → (q : a ≡ k) → ∀ (e : a ≡ a) → e ≡ refl
Kmove K refl e = K e

K→loop : ∀ {k} → KAt k → SelfLoopAt k
K→loop {k} K r = lem r refl refl
  where
  lem : ∀ {t k₀ : Cd} (r : t ⊲ k₀) (e : t ≡ k₀) → k₀ ≡ k → subst (λ z → z ⊲ k₀) e r ≡ hself
  lem {k₀ = k₀} hself e q = cong (λ e′ → subst (λ z → z ⊲ k₀) e′ hself) (Kmove K q e)
  lem (hsuc r′) e q = ⊥-elim (nos (subst (λ z → z ⊲ _) e r′))
  lem (hlim n r′) e q = ⊥-elim (nl _ hself (ppl n (subst (λ z → z ⊲ _) e r′)))
  lem (hLim {κ = ()} _ _) e q

loop-fin : ∀ {k} → NoLim k → SelfLoopAt k
loop-fin v = K→loop (K-fin v)
```

## 结论 (按档)

- **[定理]** §1 `Diag.above₊` (对一切输出 $\ge1$ 的族, 对角高于每个 $F(y_n+1)+1$), `blind-ω` (常值族 $1$: 同一形状成立, 对角 $\le\omega$). §2 `InvU`, `blockU`, **`¬MoX-u₀`**, **`¬MoX-inU₁`** (`TU 1` 的输入不在 ValX 的 `MoX` 里), **`P2-block`**, `P2-block-≤X` (经层反射关系证 P2 在 $1+\omega_1\le1+\omega_2$ 处被挡), `not⊲′`. §3 `MoX-Xn`, `MoX-Yn`, **`self-unrel`**, `MoX-C₁`, `MoX-C₂`, **`copies-unrel`**, **`copies-blind`**, `OnX⁻.self≤copy-excl⁻`. §4 **`K-fin`**, **`K-hz`**, `Kmove`, **`K→loop`**, **`loop-fin`**.
- **[判断]** `goal-if` 的 $+1$ 只来自 `oneX` (读证明); `P2` 的真假未知; UIP 对跨底值定理是否必要未知 (元定理); 带极限的层号上的 K 不用函数外延不可证.
