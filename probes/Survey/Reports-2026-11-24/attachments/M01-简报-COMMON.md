# 公共约束 (两路相同, 必须遵守)

仓库: <仓库> (只读; 不在仓库里写任何文件, 不提交, 不改 .agdai 以外的东西, 也不要对仓库模块用 --ignore-interfaces).
W4 模块 (已编译, 只读): <实验目录>/w4 (W4Block, W4Ops, W4Path, W4Fold, W4Val, W4View 的 .agda).
库文件: <实验目录>/libraries

你只在自己的工作目录里写 (见各路简报), 文件名用自己的前缀, 纯 .agda. 不在别处 rm, 不 pkill, 不写 /tmp, 不装包.

每个文件第一行的选项逐字写:
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}
无公设, 无洞, 无 TERMINATING / NO_POSITIVITY 等编译指示, 不开 K. 函数外延不准用.

编译 (同时只跑一个 agda; 从仓库根目录; 把 <目录> <文件> 换成你的):
  cd <仓库> && timeout 900 agda --library-file=<实验目录>/libraries -l standard-library-2.4 -l cubical-0.9 -i src -i probes -i <实验目录>/w4 -i <目录> <目录>/<文件>.agda +RTS -M6G -RTS > <目录>/<文件>.log 2>&1; echo $?
退出码: 0 通过; 42 类型错误或有洞 (先看日志首行是不是 LibraryError); 251 堆耗尽 (不是通过也不是类型错误, 先改形状: 陈述逐字写, 大的中间项放 opaque, 隐式参数显式写); 124 超时.
报退出码时不要经过管道. 日志落文件, 只看首个错误附近.

项目规则见 <仓库>/AGENTS.md 的 "Agda" 一节 (先读这一节). 性能问题先看 <仓库>/probes/Survey/EBOHandbook.md 的 §4.2 与 §4.6.

回报 (你的最终消息, 中文): 
1. 每个文件: 行数, 最后一次编译的退出码.
2. 每条编译通过的定理: 陈述逐字抄出 (不要改写), 一句白话说明.
3. 没做成的: 卡在哪一条, 首个错误原文, 你的判断 (标明是判断).
4. 若发现要证的命题不成立: 给最小反例, 最好是编译过的 refl 事实.
区分 "编译定理" "有限测试" "判断". 不要写没有编译过的东西是定理.
