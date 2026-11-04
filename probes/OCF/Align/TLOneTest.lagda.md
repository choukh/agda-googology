# `tH` 实验 (五): 前几项的头与界, 有限测试

> 入口 [TLOne](TLOne.lagda.md). **有限测试, 不是证明.** 比较器: `refl`, 看 `shape d`: 深度 $d$ 的形状树. 零, 后继, 极限 (看第 0, 1 项), 闭包节点 (看界, 起点 `t₀`, 第一支 `o₀`, 和 `suc c` 处的分支). 盲区: 不看值; 分支只看一个 $\eta$; 深度有限; 形状相同推不出同值 (`noCert₂` 的教训). 能否算出来本身也是测试的一部分: 算不动的写在入口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOneTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev; ⊑-suc; _⊔_)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (⌈_⌉; ωᶜ)
open import OCF.Align.LadderOrdCert using (Tᵖ)
open import OCF.Align.CrossMTop using (Tᵀ; ψ̄ᵀ; ψᵀ; ιT; Ω̇ᵀ; module 𝕎)
open import OCF.Align.CrossMClosed using (lv⊤)
open import OCF.Align.TLOneLeaf

ev₁ : Ev (suc zero) Fl
ev₁ = tt , (λ q → q)

data S : Set where
  ·  : S
  z  : S
  s  : S → S
  l  : S → S → S
  c  : S → S → S → S → S

shO : ℕ → Ordᴵ → S
shO zero _ = ·
shO (suc d) zero = z
shO (suc d) (suc a) = s (shO d a)
shO (suc d) (lim f _) = l (shO d (f 0)) (shO d (f 1))

shape : ℕ → Z → S
shape zero _ = ·
shape (suc d) Z.zero = z
shape (suc d) (Z.suc x) = s (shape d x)
shape (suc d) (Z.lim f) = l (shape d (f 0)) (shape d (f 1))
shape (suc d) (Z.ĉᴸ b t₀ g o₀ o) = c (shO d b) (shape d t₀) (shape d o₀) (shape d (o (suc b) (⊑-suc b)))

zᵒ zˢ zʳ zᶜ zᵀ : ℕ → Z
zᵀ n = toZ (Tᵀ cz (natᴵ n) ev₁ zero)
zᵒ n = toZ (Lo.Tᴸ cz (natᴵ n) ev₁ zero)
zˢ n = toZ (Ls.Tᴸ cz (natᴵ n) ev₁ zero)
zʳ n = toZ (Lr.Tᴸ cz (natᴵ n) ev₁ zero)
zᶜ n = toZ (Lc.Tᴸ cz (natᴵ n) ev₁ zero)

-- 原则版: 高度槽, α = 1; α 槽
zʰ zᵃ : Z
zʰ = toZ (Tᵖ (cs ⌈ lv⊤ ⌉) end (suc zero) ev₁ zero)
zᵃ = toZ (Tᵖ ωᶜ end (suc lv⊤) ev₁ zero)
```

`#z` 数形状树里界为 0 的闭包节点. 绑定节点 `tH` 经 `ψ̄ᵀ` 落成的正是这种节点, 世界里的行 (`qcl`, `qclo`) 落成的界不是 0 (下面的测试). 盲区: 只数到深度 $d$, 只走展开的那些支; 界是 0 不等于是绑定 (`CrossNextInst` 的 `T̂ᵀ` 根本不是闭包节点, 它也是绑定的计值).

```agda
open import Data.Nat using (_+_)

#z : S → ℕ
#z · = 0
#z z = 0
#z (s x) = #z x
#z (l x y) = #z x + #z y
#z (c z t o b) = suc (#z t + #z o + #z b)
#z (c _ t o b) = #z t + #z o + #z b

fsZ : Z → ℕ → Z
fsZ (Z.lim f) n = f n
fsZ x n = x
```

## §1 克隆就是原来的树

参数化的折叠取 `L-orig` 时, 形状与 `CrossMTop` 相同.

```agda
_ : shape 5 (zᵀ 1) ≡ shape 5 (zᵒ 1)
_ = refl

_ : shape 5 (zᵀ 0) ≡ shape 5 (zᵒ 0)
_ = refl
```

## §2 基本列: 第 $n+1$ 项就是现成规则作用在第 $n$ 项上

`Tᵀ cz 1` 的第 1 项与 `ψ̄ᵀ (ψᵀ zero (ιT zero (Ω̇ᵀ cz 0)))` 同形: 没有为这个基本列写任何规则, 它是 `tΩ` 的链. 第 0 项就是 `Tᵀ cz 0`.

```agda
_ : shape 5 (fsZ (zᵀ 1) 0) ≡ shape 5 (zᵀ 0)
_ = refl

ev₂ : Ev (suc zero) (Fl ⊔ Fl)
ev₂ = ev₁ , ev₁

item₁ : Z
item₁ = toZ (ψ̄ᵀ {M = cz} 𝕎.ok₀ (λ i → 𝕎.ok₀ i , 𝕎.ok₀ i) (ψᵀ zero (ιT zero (Ω̇ᵀ cz zero))) ev₂ zero)

_ : shape 5 (fsZ (zᵀ 1) 1) ≡ shape 5 item₁
_ = refl
```

## §3 头与界

深度 3. 头: 四片叶子和原则版在第 0, 1 项上都是极限套闭包或极限套极限, **头分不开有绑定和没绑定**. 界分得开: 绑定的是 0, 世界里的行 (`zʳ`, `zʰ`) 不是 0. 常数叶子 `zᶜ` 与 $lpha$ 槽 `zᵃ` 头两层都是极限.

```agda
_ : shape 3 (zᵀ 1) ≡ l (c z (l · ·) (l · ·) (c · · · ·)) (c z (l · ·) (l · ·) (c · · · ·))
_ = refl

_ : shape 3 (zˢ 1) ≡ l (c z (c · · · ·) (c · · · ·) (c · · · ·)) (c z (c · · · ·) (c · · · ·) (c · · · ·))
_ = refl

_ : shape 3 (zʳ 1) ≡ l (c (s ·) (l · ·) (l · ·) (l · ·)) (c (s ·) (l · ·) (l · ·) (l · ·))
_ = refl

_ : shape 3 zʰ ≡ l (c (s ·) (l · ·) (l · ·) (l · ·)) (c (s ·) (l · ·) (l · ·) (l · ·))
_ = refl

_ : shape 3 (zᶜ 1) ≡ l (l (l · ·) (l · ·)) (l (l · ·) (l · ·))
_ = refl

_ : shape 3 zᵃ ≡ l (l (l · ·) (l · ·)) (l (l · ·) (l · ·))
_ = refl
```

## §4 绑定的叶子进了折叠

第 1 项里界为 0 的闭包节点: `L-orig` 有, 没绑定的都没有.

```agda
_ : #z (shape 9 (fsZ (zᵀ 1) 1)) ≡ 55
_ = refl

_ : #z (shape 9 (fsZ (zʳ 1) 1)) ≡ 0
_ = refl

_ : #z (shape 7 zʰ) ≡ 0
_ = refl

_ : #z (shape 7 zᵃ) ≡ 0
_ = refl
```
