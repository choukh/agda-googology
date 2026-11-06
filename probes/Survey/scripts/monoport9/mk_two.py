# 从 MonoPort8Sim 的 §6-§7 生成 MonoPort9Two: 只在不含 Ω-极限的目标上比的互模拟
# 用法: python3 mk_two.py <仓库根>
import sys, os
root = sys.argv[1]
src = open(os.path.join(root, 'probes/OCF/Align/MonoPort8Sim.lagda.md')).read()
i = src.index('## 6 两个实例, 两个世界')
j = src.index('## 8 闭项')
body = src[i:j]

def rep(old, new, count=None):
    global body
    n = body.count(old)
    if n == 0 or (count is not None and n != count):
        raise SystemExit('pattern count mismatch (%d): %r' % (n, old))
    body = body.replace(old, new)

rep('module Two (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) (fr : ∀ {t m m′} → t ⊲[ m ] Λ₁ → t ⊲[ m′ ] Λ₂ → Free t) where',
    'module TwoF (Λ₁ : H) (l₁ : LgH Λ₁) (Λ₂ : H) (l₂ : LgH Λ₂) (frk : ∀ {W₀ W k ly} → StH W₀ k ly → ly ⊲[ W ] Λ₁ → Free k) where', 1)
rep('at : ∀ {t m m′} (wm : W ⊲ m)', 'at : ∀ {t m m′} (ft : Free t) (wm : W ⊲ m)', 1)
rep('dfe (λ wm wm′ tm₁ tm₂ lm lm′ →', 'dfe (λ ft wm wm′ tm₁ tm₂ lm lm′ →')
rep('dfe (λ {t} wm wm′ tm₁ tm₂ lm lm′ →', 'dfe (λ {t} ft wm wm′ tm₁ tm₂ lm lm′ →', 1)
rep('(ΩdE t (fr tm₁ tm₂) accᴸ)', '(ΩdE t ft accᴸ)', 1)
rep(' wm wm′ tm₁ tm₂ lm lm′)', ' ft wm wm′ tm₁ tm₂ lm lm′)')
rep('(⊲-tr q wm) (⊲-tr q′ wm′) tm₁ tm₂ lm lm′)', 'ft (⊲-tr q wm) (⊲-tr q′ wm′) tm₁ tm₂ lm lm′)', 1)
# 判定一致
rep('rkT-rel : ∀ {k t m m′} (km₁', 'rkT-rel : ∀ {k t m m′} → Free t → (km₁', 1)
rep('rkT-rel km₁ tm₁ lm km₂ tm₂ lm′ = rk-rel (fr tm₁ tm₂) _ _', 'rkT-rel ft km₁ tm₁ lm km₂ tm₂ lm′ = rk-rel ft _ _', 1)
rep('(rkT-rel (⊲ᴴ↑ wm', '(rkT-rel ft (⊲ᴴ↑ wm', 1)
# RKi-E
rep('(wm : W₁ ⊲ m) (wm′ : W₂ ⊲ m′) (tm₁ : t ⊲[ m ] Λ₁)', '(ft : Free t) (wm : W₁ ⊲ m) (wm′ : W₂ ⊲ m′) (tm₁ : t ⊲[ m ] Λ₁)', 1)
rep('hA hw hY wm wm′ tm₁ tm₂ lm lm′ (kp {R} {R′}) =', 'hA hw hY ft wm wm′ tm₁ tm₂ lm lm′ (kp {R} {R′}) =', 1)
rep('hA hw hY wm wm′ tm₁ tm₂ lm lm′ rs =', 'hA hw hY ft wm wm′ tm₁ tm₂ lm lm′ rs =', 1)
rep('hw hY wm wm′ tm₁ tm₂ lm lm′\n', 'hw hY ft wm wm′ tm₁ tm₂ lm lm′\n', 1)
rep('         C.self C.self (⊲ᴴ↑ p tm₁)', '         ft C.self C.self (⊲ᴴ↑ p tm₁)', 1)
# Chn-E: 节点层不含 Ω-极限
rep('Chn-E   : ∀ {k W₁ W₂} (ac′₁', 'Chn-E   : ∀ {k W₁ W₂} (fk : Free k) (ac′₁', 1)
rep('Chn-E ac′₁ ac′₂ hk₁', 'Chn-E fk ac′₁ ac′₂ hk₁')
rep('Chn-E ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁)', 'Chn-E (frk r₁ ll₁) ac′₁ ac′₂ (F₁.kk r₁ q₁ ll₁)')
rep('at (dE hY) C.self C.self hk₁ hk₂ lW₁ lW₂', 'at (dE hY) fk C.self C.self hk₁ hk₂ lW₁ lW₂', 1)
rep('        C.self C.self hk₁ hk₂ lW₁ lW₂ ,', '        fk C.self C.self hk₁ hk₂ lW₁ lW₂ ,', 1)
body = body.replace('## 6 两个实例, 两个世界', '## 1 两个实例, 两个世界, 只比不含 Ω-极限的目标')
body = body.replace('## 7 折叠, 逐个对应', '## 2 折叠, 逐个对应')

head = '''```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort9Two where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅)
import OCF.Align.HtFeedFold as Fold
open import OCF.Align.HtCrossVSim using (Free)
open import OCF.Align.HtCrossVRun using (module Val)
open import OCF.Align.MonoPort8Sim using (SimE; e0; e1; e⨾; el; ei; ew; RelE; Re; toE; ofE; convE; ΩdE; IntE; reS)
```

'''
hdr = open(os.path.join(root, 'probes/Survey/scripts/monoport9/two_header.md')).read()
open(os.path.join(root, 'probes/OCF/Align/MonoPort9Two.lagda.md'), 'w').write(hdr + head + body)
