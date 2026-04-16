# 模糊德摩根公式

最常见的 **Zadeh 型模糊运算**：

- 合取：$\;a\wedge b=\min(a,b)$
- 析取：$\;a\vee b=\max(a,b)$
- 否定：$\;\neg a=1-a$

那么模糊德摩根公式就是：

$$
1-\min(a,b)=\max(1-a,1-b)
$$

$$
1-\max(a,b)=\min(1-a,1-b)
$$

也可以写成熟悉的逻辑形式：

$$
\neg(a\wedge b)=\neg a\vee \neg b
$$

$$
\neg(a\vee b)=\neg a\wedge \neg b
$$

---

# 二、为什么成立：一步一步算

## 1. 证明
$$
1-\min(a,b)=\max(1-a,1-b)
$$

分两种情况。

### 情况 1：$a\le b$

那么

$$
\min(a,b)=a
$$

所以左边：

$$
1-\min(a,b)=1-a
$$

又因为 $a\le b$，所以

$$
1-a \ge 1-b
$$

于是右边：

$$
\max(1-a,1-b)=1-a
$$

所以左右相等。

---

### 情况 2：$b\le a$

同理，

$$
\min(a,b)=b
$$

左边：

$$
1-\min(a,b)=1-b
$$

又因为 $b\le a$，所以

$$
1-b\ge 1-a
$$

右边：

$$
\max(1-a,1-b)=1-b
$$

所以左右相等。

---

因此：

$$
1-\min(a,b)=\max(1-a,1-b)
$$

成立。

---

## 2. 证明
$$
1-\max(a,b)=\min(1-a,1-b)
$$

也是分两种情况。

### 情况 1：$a\ge b$

则

$$
\max(a,b)=a
$$

左边：

$$
1-\max(a,b)=1-a
$$

又因为 $a\ge b$，所以

$$
1-a\le 1-b
$$

于是右边：

$$
\min(1-a,1-b)=1-a
$$

---

### 情况 2：$b\ge a$

同理可得：

$$
1-\max(a,b)=1-b=\min(1-a,1-b)
$$

所以

$$
1-\max(a,b)=\min(1-a,1-b)
$$

成立。

---

$\forall\bigcirc\phi$ 的证明时，出现了这种变形：

$$
\bigwedge_i a_i
=
\left(\bigvee_i a_i^c\right)^c
$$

这里的 $a_i^c$ 就表示补：

$$
a_i^c=1-a_i
$$

这其实就是把二元德摩根律推广到有限个元素的版本。

也就是：

$$
\neg(a_1\wedge a_2\wedge \cdots \wedge a_n)
=
\neg a_1\vee \neg a_2\vee \cdots \vee \neg a_n
$$

等价地写成：

$$
a_1\wedge a_2\wedge \cdots \wedge a_n
=
\neg(\neg a_1\vee \neg a_2\vee \cdots \vee \neg a_n)
$$

在 Zadeh 语义下就是：

$$
\bigwedge_i a_i
=
\left(\bigvee_i (1-a_i)\right)^c
$$

也就是你看到的

$$
\bigwedge_i a_i
=
\left(\bigvee_i a_i^c\right)^c
$$

---

# 五、再说一个容易混淆的点

“模糊德摩根公式”**不是在所有模糊逻辑系统里都自动成立成这个样子**。

它依赖你选的三样东西是否匹配：

- 合取怎么定义
- 析取怎么定义
- 否定怎么定义

如果你采用的是：

- $\min$
- $\max$
- $1-a$

那么上面这套德摩根律完全成立。

但如果你换成别的 t-norm、t-conorm、否定函数，形式可能会变，甚至未必严格成立成这一个样子。

所以你这篇文章里之所以能直接这么用，是因为它默认采用的是这种最常见、最标准的模糊运算体系。

---



“这里用到的是模糊德摩根公式。在 Zadeh 型模糊逻辑中，合取取最小值、析取取最大值、否定定义为 $1-a$。因此有
$$
1-\min(a,b)=\max(1-a,1-b),\qquad 1-\max(a,b)=\min(1-a,1-b)
$$
也就是
$$
\neg(a\wedge b)=\neg a\vee \neg b,\qquad \neg(a\vee b)=\neg a\wedge \neg b
$$
进一步可推广为
$$
\bigwedge_i a_i=\left(\bigvee_i a_i^c\right)^c
$$
所以文中才能把全称 next 里的大合取改写成补矩阵与全 1 向量的形式。”



