# 论文讲解 PPTL BMC

#### You:
讲解一下这篇论文

#### Plugin (file_search):
Make sure to include fileciteturn0file0 in your response to cite this file, or to surface it as a link.
<PARSED TEXT FOR PAGE: 1 / 17>
Theoretical Computer Science 1049 (2025) 115368
Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
Contents lists available at ScienceDirect
Theoretical Computer Science
journal homepage: www.elsevier.com/locate/tcs
SAT-based bounded model checking for propositional projection
temporal logic ✩
Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a
a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China b China Academy of Space Technology, Beijing 100094, China
A R T I C L E I N F O A B S T R A C T
Section Editor: Paul G. Spirakis
Handling Editor: Ding-Zhu Du
Keywords:
Propositional projection temporal logic
Bounded model checking
Rate monotonic scheduling
This paper presents a bounded model checking (BMC) approach for propositional projection
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed
in the paper is useful and feasible.
1. Introduction
Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted,
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware,
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀⊧𝜙?). With temporal logics, linear-time temporal
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8]
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9].
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC)
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs.
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC
✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.
* Corresponding authors.
E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn
(C. Yu), yangmf@bice.org.cn (M. Yang).
https://doi.org/10.1016/j.tcs.2025.115368
Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025
<PARSED TEXT FOR PAGE: 2 / 17>
Theoretical Computer Science 1049 (2025) 115368
2
Z. Duan, C. Tian, N. Zhang et al.
is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥.
As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors
such as EBMC [20] are used in the verification of large-scale hardware and software systems.
Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.
With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach,
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.
The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the
conclusion is drawn in section 8.
2. Propositional projection temporal logic
To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL)
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to
[26].
2.1. Syntax:
PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:
𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑃
where 𝑝 ∈ 𝑃 𝑟𝑜𝑝 and 𝑃,𝑃1,…, 𝑃𝑖,…, 𝑃𝑙,…, 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙, 𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal
operators, otherwise it is called a temporal formula.
2.2. Semantics:
Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 = 𝑁 ∪ {𝜔} and extend
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁, 𝑖 < 𝜔, 𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as
≤ −{(𝜔,𝜔)}.
A state 𝑠𝑖 is a mapping from 𝑃 𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠|𝜎|⟩.
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote
the subinterval ⟨𝑠𝑖,…, 𝑠𝑗 ⟩ and 𝜎(𝑘)
(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,…, 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔
while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗<𝑖, in this case, 𝜎(𝑖..𝑗) = . Note that, 
denotes void (for nothing) and its length || is -1.
Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.
<PARSED TEXT FOR PAGE: 3 / 17>
Theoretical Computer Science 1049 (2025) 115368
3
Z. Duan, C. Tian, N. Zhang et al.
Fig. 1. Projected Intervals.
Fig. 2. Three cases of (𝑃1,…, 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)
𝜎1 ⋅ 𝜎2 =
⎧
⎪
⎪
⎨
⎪
⎪
⎩
𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ,
𝜎2, if 𝜎1 = ,
⟨𝑠0,…, 𝑠𝑖, 𝑠𝑖+1,…, 𝑠𝑗 ⟩, if 𝜎1 = ⟨𝑠0,…, 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,…, 𝑠𝑗 ⟩,
𝑗 ≤ 𝜔,|𝜎1| ≠ 𝜔.
It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1| + |𝜎2| and for any interval 𝜎,  ⋅ 𝜎 = 𝜎 ⋅  = 𝜎.
For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the
same successive state to produce different projected states, we define the projected interval:
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚) = ⟨𝑠𝑡0
, 𝑠𝑡1
,…, 𝑠𝑡𝑛
⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ …𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁, and 𝑡0, 𝑡1,…, 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,…, 𝑟𝑚 by deleting
all duplicates. That is, 𝑡0,…, 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,…, 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case,
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1, 𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected
intervals are given below (See Fig. 1).
(a) ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 3, 4, 4, 4, 6) = ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 4, 6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0, 0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47, 47, 𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47) = ⟨𝑠0, 𝑠21, 𝑠47⟩
Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1,…, 𝑃𝑚 are interpreted
in the projection construct. In order to interpret the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞
as follows:
Let 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠𝑚,…, 𝑠𝑗 ⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is
interpreted over a subinterval 𝜎(𝑟𝑖−1..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,…, 𝑠𝑟𝑖
⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination
of 𝑃𝑚 (see red color sequence).
Thus, we define 𝜎𝑞 as follows:
𝜎(𝑟𝑚+1..𝑗) =
{ < 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,
, if 𝑟𝑚 = 𝑗.
𝜎𝑞 = 𝜎 ↓ (𝑟0,…, 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)
<IMAGE FOR PAGE: 3 / 17>
![image](sediment://7a41b68aec6f5e2#file_00000000677c7209a156353e1c071784#p_2.jpg)
<PARSED TEXT FOR PAGE: 4 / 17>
Theoretical Computer Science 1049 (2025) 115368
4
Z. Duan, C. Tian, N. Zhang et al.
Table 1
Derived formulas.
A1 𝜀
def
= ¬ ○ ⊤ A2 𝜖def
= ○⊤
A3 ⨀𝑃 def
= 𝜀 ∨ ○𝑃 A4 𝑃 ;𝑄 def
= (𝑃,𝑄) 𝑝𝑟𝑗 𝜀
A5 ◊ 𝑃 def
= ⊤;𝑃 A6 □𝑃 def
= ¬◊¬𝑃
A7 𝑓 𝑖𝑛 def
= ◊𝜀 A8 𝑖𝑛𝑓 def
= ¬𝑓 𝑖𝑛
A9 {
○0𝑃 def
= 𝑃
○𝑛𝑃 def
= ○(○𝑛−1𝑃 )(𝑛 > 0)
A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧ 𝑄 ∨ 𝑃 ∧ (𝑄;⊤)
∨𝑃 ∧ 𝑄 ∧ □ 𝜖
A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)
𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.
PPTL formulas are interpreted over intervals. An interpretation  = (𝜎, 𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,…, 𝑠𝑗 ⟩ of 𝜎 with the current state
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎⊧𝑃
if 𝜎(0,|𝜎|) ⊧ 𝑃 .
(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.
(2)  ⊧ ○𝑃 iff 𝑘<𝑗 and (𝜎,𝑘 + 1, 𝑗) ⊧ 𝑃 .
(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .
(4)  ⊧ 𝑃 ∨ 𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.
(5)  ⊧ (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎,𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all
1 ≤ 𝑙 ≤ 𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞 , 0,|𝜎𝑞 |) ⊧ 𝑄).
Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎⊧𝑝, if (𝜎, 0,|𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable
if 𝜎⊧𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎⊧𝑝 for all 𝜎.
Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤ def
= 𝑃 ∨ ¬𝑃 and ⊥ def
= 𝑃 ∧ ¬𝑃 , for any
formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.
2.3. Normal form
Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL
formula 𝑄. Then, the NF can be defined as follows:
Definition 1. Normal Form of 𝑄:
𝑁𝐹(𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀)∨∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧ ○𝑄′
𝑖
)
To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟
𝑖=1(𝑄𝑖 ∧ ○𝑄′
𝑖
) to replace
∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧ ○𝑄′
𝑖
). Thus,
𝑁𝐹(𝑄) ≡ 𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧ ○𝑄′
𝑖
)
where 𝑄𝑒 and 𝑄𝑖 are state formulas.
Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.
The proof of this theorem can be found in [26].
Example 1. Given a PPTL formula 𝑓, 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get
𝑁𝐹(𝑓) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀)∨(𝑟 ∧ 𝑝 ∧ ○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ ○⊤)∨(𝑟 ∧ 𝑝 ∧ ○(⊤; (𝑞;⊤)))
3. Principle of SAT-based bounded model checking with PPTL
In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖
. In the following, we define the bounded semantics of PPTL formulas.
Let 𝜎 be an interval and 𝑃 a PPTL formula.
<PARSED TEXT FOR PAGE: 5 / 17>
Theoretical Computer Science 1049 (2025) 115368
5
Z. Duan, C. Tian, N. Zhang et al.
Fig. 3. 𝜎 is a 𝑘 − 𝑙𝑜𝑜𝑝.
3.1. Bounded semantics
In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.
Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼,𝑇,𝐿) where 𝑆 is the set of sates, 𝐼⊆𝑆 is the set of initial states,
𝑇 ⊆𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.
We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite.
Therefore, in the following, we give the definition of 𝑘 − 𝑙𝑜𝑜𝑝 in an interval.
Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,…, 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,…, 𝑠𝑘⟩𝜔, we call
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.
Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈ 𝑁0. Now we can define the successor of state
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:
𝑠𝑢𝑐𝑐(𝑖) =
⎧
⎪
⎨
⎪
⎩
𝑖 + 1 if 𝑖<𝑘
𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝
𝑘 + 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval
With bounded model checking of PPTL, given a bound 𝑘 ∈ 𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval
< 𝑠𝑖,…, 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .
The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:
(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃 𝑟𝑜𝑝 is an atomic proposition
(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃
(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃
(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘
(𝜎, 𝑖) ⊧𝑘
𝜖 iff 𝑖<𝑘
A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎, 0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have
𝜎 ⊧𝑘 𝑃 iff (𝜎, 0, 𝑘) ⊧ 𝑃 .
As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics
of PPTL is sound.
3.2. Bounded model checking
According to the structure of interval 𝜎, two basic lemmas are given below:
Lemma 1. Let 𝑘 ∈ 𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘 − 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎⊧𝑓.
Proof. To prove Lemma 1, we first prove a stronger conclusion given below:
(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)
Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓:
Base case:
𝑓 ≡ 𝑝 ∈ 𝑃 𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖,|𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑝.
<PARSED TEXT FOR PAGE: 6 / 17>
Theoretical Computer Science 1049 (2025) 115368
6
Z. Duan, C. Tian, N. Zhang et al.
Fig. 4. 𝜎 is a finite interval.
Inductive cases:
1. Suppose for any PPTL formula 𝑓, (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Then, we have, (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 iff (𝜎, 𝑖,|𝜎|) ̸⊧ 𝑓. Further,
(𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 and (𝜎, 𝑖,|𝜎|) ⊧ ¬𝑓 iff (𝜎, 𝑖,|𝜎|) ̸⊧ 𝑓, leading to (𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ ¬𝑓.
2. Suppose for any PPTL formula 𝑓, (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Since 𝜎 is a 𝑘 − 𝑙𝑜𝑜𝑝, so, 𝑠𝑢𝑐𝑐(𝑖) ≤ 𝑘 < |𝜎|. Then, by
hypothesis, we have,
(𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖),|𝜎|) ⊧ 𝑓. By the definitions of semantics, (𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 ○𝑓
iff (𝜎, 𝑖, 𝑘) ⊧ ○𝑓 and (𝜎, 𝑠𝑢𝑐𝑐(𝑖),|𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖 + 1,|𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ ○𝑓, so (𝜎, 𝑖, 𝑘) ⊧ ○𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ ○𝑓.
3. Suppose for any PPTL formulas 𝑓1 and 𝑓2, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓1 and (𝜎, 𝑖, 𝑘) ⊧ 𝑓2 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓2. Then, by the
definitions of bounded semantics and model semantics, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 ∨ 𝑓2 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓1 ∨ 𝑓2. □
Note that we do not need to deal with 𝜀 and 𝜖
in the above inductive cases since 𝜀 ≡ ¬ ○ ⊤ and 𝜖
≡ ○⊤.
Lemma 2. Let f be a PPTL formula, and 𝜎 a finite interval (Fig. 4). Then 𝜎⊧𝑓 ⇒ ∃𝑘, 𝑘 ≥ 0,𝜎⊧𝑘 𝑓.
Proof. Since 𝜎 is a finite interval, so |𝜎| ∈ 𝑁0.
𝜎⊧𝑓 ⇔ (𝜎, 0,|𝜎|) ⊧ 𝑓
⇔ (𝜎, 0, 𝑘) ⊧ 𝑓 ∧ 𝑘 = |𝜎|
⇒ ∃𝑘, 𝑘 ≥ 0,(𝜎, 0) ⊧𝑘 𝑓
⇔ ∃𝑘, 𝑘 ≥ 0,𝜎⊧𝑘 𝑓 □
Theorem 2. Suppose a system is described by a Kripke structure M, and some property is defined by a PPTL formula 𝑓. Let 𝑀 be the set
of all intervals generated in M. We define 𝑀 ⊧ ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 as well as 𝑀 ⊧𝑘 ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓. Then we have
𝑀 ⊧ ∃𝑓 iff ∃𝑘, 𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓.
Proof. We need prove that ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓. To do so, we consider intervals in 𝑀 as infinite or finite ones
respectively.
1. Suppose 𝜎 is infinite, there must be an integer 𝑘 ≥ 0 that makes 𝜎 a 𝑘 − 𝑙𝑜𝑜𝑝. By Lemma 1:
𝜎 ⊧𝑘 𝑓 iff 𝜎⊧𝑓
we have,
𝑀 ⊧ ∃𝑓 iff ∃𝑘, 𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓
2. Suppose interval 𝜎 is finite, i.e., |𝜎| = 𝑚 ∈ 𝑁0.
“ ⇒ ” ∶ 𝑀 ⊧ ∃𝑓 ⇔ ∃𝜎 ∈ 𝑀 ∧ 𝜎⊧𝑓 ⇒ ∃𝑘, 𝑘 ≥ 0,∃𝜎 ∈ 𝑀 ∧ 𝜎 ⊧𝑘 𝑓
⇔ ∃𝑘, 𝑘 ≥ 0,Σ ⊧𝑘 ∃𝑓 (Lemma 2)
“ ⇐ ” ∶ ∃𝑘, 𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝑘, 𝑘 ≥ 0,∃𝜎 ∈ 𝑀 ∧ 𝜎 ⊧𝑘 𝑓
⇔ ∃𝑘, 𝑘 ≥ 0,∃𝜎 ∈ 𝑀 ∧ (𝜎, 0) ⊧𝑘 𝑓
⇔ ∃𝑘, 𝑘 ≥ 0,∃𝜎 ∈ 𝑀 ∧ (𝜎, 0, 𝑘) ⊧ 𝑓
Let 𝜎′ =< 𝑠0, 𝑠1,…, 𝑠𝑘 >, we have (𝜎′
, 0, 𝑘) ⊧𝑓. Since 𝜎′ is a subinterval
of 𝜎 and |𝜎′
| = 𝑘, hence, ∃𝜎′ ∈ 𝑀 and 𝜎′ ⊧𝑓, leading to 𝑀 ⊧ ∃𝑓.
As a result, ∃𝑘, 𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇒ 𝑀 ⊧ ∃𝑓. □
3.3. Reducing bounded model checking with PPTL to SAT
Given a finite state transition system 𝑀 (a Kripke structure or NFG), the property of the system in terms of a PPTL formula 𝑓, and
a bound 𝑘, then the procedure of BMC can be described as a process for constructing a proposition formula [𝑀,𝑓]𝑘. Let ⟨𝑠0,…, 𝑠𝑘⟩ be
a subinterval of interval 𝜎. The definition of formula [𝑀,𝑓]𝑘 consists of two components: 𝑀𝑘, the first component, is a propositional
formula that constrains ⟨𝑠0,…, 𝑠𝑘⟩ to be a valid interval starting from an initial state; 𝑋𝑘, the second component, a propositional
<PARSED TEXT FOR PAGE: 7 / 17>
Theoretical Computer Science 1049 (2025) 115368
7
Z. Duan, C. Tian, N. Zhang et al.
formula that constrains 𝜎 to satisfy 𝑓 with bound 𝑘. To define the second component, we first give the definition of 𝑙𝑜𝑜𝑝 𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛,
which is a propositional formula that is evaluated to true only if the interval 𝜎 contains a loop; then we give some translation rules
for formulas.
Definition 4. For a Kripke structure M, and k ≥ 0,
𝑀𝑘
def
= 𝐼(𝑠0)∧∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1)
Loop condition:
𝐿(𝑘,𝑙)
def
= 𝑇 (𝑠𝑘, 𝑠𝑙) (0 ≤ 𝑙 ≤ 𝑘)
𝐿𝑘
def
= ∨𝑘
𝑙=0 𝐿(𝑘,𝑙)
Let 𝑝 be an atomic proposition, and 𝑓, 𝑔 be PPTL formulas, 𝜎 an interval with a (𝑘, 𝑙) −𝑙𝑜𝑜𝑝, 𝑠𝑖 the current state, and 𝑘 the bound,
where 0 ≤ 𝑖, 𝑙, 𝑘 ≤ |𝜎|, 𝑖, 𝑙 ≤ 𝑘. The translation of a PPTL formula is given below:
k-loop: Translation 𝑓(𝑖, 𝑘, 𝑙) of a PPTL formula 𝑓 over an infinite interval 𝜎 with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 is inductively defined as follows.
𝑝(𝑖,𝑘,𝑙)
def
= 𝑝(𝑠𝑖) if 𝑝 ∈ 𝑃 𝑟𝑜𝑝 is an atomic proposition, meaning 𝑠𝑖[𝑝]
(¬𝑓)(𝑖,𝑘,𝑙)
def
= ¬𝑓(𝑖,𝑘,𝑙)
(𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙)
def
= 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙)
(○𝑓)(𝑖,𝑘,𝑙)
def
= 𝑓(𝑠𝑢𝑐𝑐(𝑖),𝑘,𝑙)
𝜀(𝑖,𝑘,𝑙)
def
=
{ ⊥ 𝑖<𝑘
⊤ 𝑖 = 𝑘
𝜖
(𝑖,𝑘,𝑙)
def
=
{ ⊤ 𝑖<𝑘
⊥ 𝑖 = 𝑘
For the translation presented above, a new propositional variable is introduced for each intermediate formula 𝑒(𝑖,𝑘,𝑙), where 𝑒 is a
sub-formula of PPTL formula 𝑓 and 0 ≤ 𝑖 ≤ 𝑘 and 𝑙 indicates the existence of (𝑘, 𝑙) −𝑙𝑜𝑜𝑝. If 𝑒 is an atomic proposition or its negation,
𝑒(𝑖,𝑘,𝑙) is substituted by a boolean variable with the truth-value at state 𝑠𝑖. Otherwise, 𝑒(𝑖,𝑘,𝑙) indicates a propositional formula whose
satisfiability should be considered over the interval (𝑠𝑖,…, 𝑠𝑘).
no loop: Translation 𝑓(𝑖, 𝑘) of a PPTL formula 𝑓 for a finite interval 𝜎 (with no loop).
𝑝(𝑖,𝑘)
def
= 𝑝(𝑠𝑖)
(¬𝑓)(𝑖,𝑘)
def
= ¬𝑓(𝑖,𝑘)
(𝑓 ∨ 𝑔)(𝑖,𝑘)
def
= 𝑓(𝑖,𝑘) ∨ 𝑔(𝑖,𝑘)
(○𝑓)(𝑖,𝑘)
def
= 𝑓(𝑖+1,𝑘)
𝑓(𝑘+1,𝑘)
def
= ⊥
𝜀(𝑖,𝑘)
def
=
{ ⊥ 𝑖<𝑘
⊤ 𝑖 = 𝑘
𝜖
(𝑖,𝑘)
def
=
{ ⊤ 𝑖<𝑘
⊥ 𝑖 = 𝑘
When the intermediate formula 𝑒(𝑖,𝑘) appears in a PPTL formula for a finite interval (with no loop), the explanations are similar to
the ones for a PPTL formula with an interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 and omitted here.
General translation (BMC to SAT):
𝑋𝑘
def
= (¬𝐿𝑘 ∧ 𝑓(0,𝑘))∨∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))
[𝑀,𝑓]𝑘
def
= 𝑀𝑘 ∧ 𝑋𝑘
i.e.:
[𝑀,𝑓]𝑘
def
= 𝐼(𝑠0)∧∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘))∨∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))]
<PARSED TEXT FOR PAGE: 8 / 17>
Theoretical Computer Science 1049 (2025) 115368
8
Z. Duan, C. Tian, N. Zhang et al.
As we can see, the right side of the definition can be divided into two parts: the first part 𝐼(𝑠0)∧∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (¬𝐿𝑘 ∧ 𝑓(0,𝑘))
indicates an interval with no loop and the translation without loop is used; the second part 𝐼(𝑠0)∧∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧
𝑓(0,𝑘,𝑙))) presents that an interval with a 𝑘 − 𝑙𝑜𝑜𝑝 and all possible starting points 𝑙 of a loop and the translation for a 𝑘 − 𝑙𝑜𝑜𝑝 is
conjoined with the corresponding loop condition 𝐿(𝑘,𝑙).
Lemma 3. Let 𝑘 ∈ 𝑁0, 𝑓 be a PPTL formula and 𝜎 an interval. The translation 𝑓(𝑖,𝑘,𝑙) or 𝑓(𝑖,𝑘) is defined as above. Then
(1) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘,𝑙) if 𝜎 is infinite with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 or
(2) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘) if 𝜎 is finite.
Proof. We prove only (1) but in a stronger version. A similar proof can be given to prove (2). The proof proceeds by induction on
the rules of the definition of translation.
Base: for an atomic proposition 𝑝 ∈ 𝑃 𝑟𝑜𝑝.
(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ while (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙) iff 𝜎 ⊧𝑘 𝑝(𝑠𝑖) iff 𝑠𝑖[𝑝] = ⊤. So, (𝜎, 𝑖) ⊧𝑘 𝑝 iff (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙)
Induction:
Suppose (𝜎, 𝑖) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙), (𝜎, 𝑖) ⊧𝑘 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙). We have,
1) (𝜎, 𝑖) ⊧𝑘 ¬𝑓 iff (𝜎, 𝑖) ̸⊧𝑘 𝑓 def
iff (𝜎, 𝑖) ̸⊧𝑘 𝑓(0,𝑘,𝑙) hypothesis
iff (𝜎, 𝑖) ⊧𝑘 ¬𝑓(0,𝑘,𝑙) def
iff (𝜎, 𝑖) ⊧𝑘 (¬𝑓)(0,𝑘,𝑙) def
2) (𝜎, 𝑖) ⊧𝑘 𝑓 ∨ 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑓 or (𝜎, 𝑖) ⊧𝑘 𝑔 def
iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) or (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙) hypothesis
iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙) def
iff (𝜎, 𝑖) ⊧𝑘 (𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙) def
3) (𝜎, 𝑖) ⊧𝑘 ○𝑓 iff (𝜎, 𝑖) ⊧ ○𝑓 Lemma 1
iff (𝜎, 𝑖 + 1) ⊧ 𝑓 Def
iff (𝜎, 𝑖 + 1) ⊧ 𝑓(𝑖,𝑘,𝑙) hypothesis
iff (𝜎, 𝑖) ⊧ (○𝑓)(𝑖,𝑘,𝑙) def
iff (𝜎, 𝑖) ⊧𝑘 (○𝑓)(𝑖,𝑘,𝑙) Lemma 1
We do not need to consider 𝜀 and 𝜖
again here. When 𝑖 = 0 the Lemma 3 is proved. Now we come to prove an important conclusion
formalized in Theorem 3.
Theorem 3. [𝑀,𝑓]𝑘 is satisfiable iff M ⊧𝑘 ∃ f.
Proof. ``⇒'': Suppose [𝑀,𝑓]𝑘 is satisfiable. That is, ∃𝑘 ≥ 0, 𝜎 ∈ 𝑀,𝜎 ⊧ [𝑀,𝑓]𝑘 ⇔ 𝜎⊧𝑀𝑘 ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘))∨∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))].
If |𝜎| = 𝜔 with (𝑘, 𝑙)-loop and 𝑙 ≤ 𝑘, we have,
𝜎 ⊧ [𝑀,𝑓]𝑘 ⇒ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙)) def of [𝑀,𝑓]𝑘
⇒ 𝜎 ⊧ ∃𝑗 0 ≤ 𝑗 ≤ 𝑘 𝑓(0,𝑘,𝑗)
⇒ 𝜎⊧𝑓(0,𝑘,𝑗) (0 ≤ 𝑗 ≤ 𝑘)
⇒ 𝜎 ⊧𝑘 𝑓(0,𝑘,𝑗) (0 ≤ 𝑗 ≤ 𝑘) Lemma 1
⇒ 𝜎 ⊧𝑘 𝑓 Lemma 3
⇒ ∃𝑘 𝑘 ≥ 0, 𝜎 ∈ 𝑀𝜎⊧𝑘 𝑓
⇒ 𝑀 ⊧𝑘 ∃𝑓 def
If |𝜎| ∈ 𝑁0 with no loop, we have,
𝜎 ⊧ [𝑀,𝑓]𝑘 ⇒ 𝜎⊧𝑓(0,𝑘) def of [𝑀,𝑓]𝑘
⇒ ∃𝑘𝑘 ≥ 0,𝜎⊧𝑘 𝑓(0,𝑘) Lemma 1
⇒ ∃𝑘𝑘 ≥ 0, 𝜎 ∈ 𝑀 𝜎⊧𝑘 𝑓 Lemma 3
⇒ 𝑀 ⊧�
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn0file1 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 , 𝑠𝑡1 ,… , 𝑠𝑡𝑛 ⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ … 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁 , and 𝑡0, 𝑡1,… , 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,… , 𝑟𝑚 by deleting 
all duplicates. That is, 𝑡0,… , 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,… , 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case, 
𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1,𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected 
intervals are given below (See Fig. 1).

(a) ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,3,4,4,4,6) = ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,4,6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0,0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47,47,𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47) = ⟨𝑠0, 𝑠21, 𝑠47⟩

Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1 ,… , 𝑃𝑚 are interpreted 
in the projection construct. In order to interpret the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞

as follows:

Let 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠𝑚,… , 𝑠𝑗⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is 
interpreted over a subinterval 𝜎(𝑟𝑖−1 ..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,… , 𝑠𝑟𝑖⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in 
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination 
of 𝑃𝑚 (see red color sequence).

Thus, we define 𝜎𝑞 as follows:

𝜎(𝑟𝑚+1..𝑗) =

{
< 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,

ε, if 𝑟𝑚 = 𝑗.

𝜎𝑞 = 𝜎 ↓ (𝑟0,… , 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)



Theoretical Computer Science 1049 (2025) 115368

4

Z. Duan, C. Tian, N. Zhang et al. 

Table 1
Derived formulas.

A1 𝜀
def
= ¬○⊤ A2 𝜖def= ○⊤

A3 ⨀
𝑃

def
= 𝜀 ∨○𝑃 A4 𝑃 ;𝑄

def
= (𝑃 ,𝑄) 𝑝𝑟𝑗 𝜀

A5 ◊ 𝑃
def
= ⊤;𝑃 A6 □𝑃

def
= ¬◊¬𝑃

A7 𝑓𝑖𝑛
def
= ◊𝜀 A8 𝑖𝑛𝑓

def
= ¬𝑓𝑖𝑛

A9

{
○0𝑃

def
= 𝑃

○𝑛𝑃
def
= ○(○𝑛−1𝑃 )(𝑛 > 0)

A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧𝑄 ∨ 𝑃 ∧ (𝑄;⊤)

∨𝑃 ∧𝑄 ∧□

𝜖

A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)

𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.

PPTL formulas are interpreted over intervals. An interpretation  = (𝜎,𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,… , 𝑠𝑗⟩ of 𝜎 with the current state 
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎 ⊧ 𝑃

if 𝜎(0, |𝜎|) ⊧ 𝑃 .

(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.

(2)  ⊧○𝑃 iff 𝑘 < 𝑗 and (𝜎,𝑘+ 1, 𝑗) ⊧ 𝑃 .

(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .

(4)  ⊧ 𝑃 ∨𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.

(5)  ⊧ (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎, 𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all 
1 ≤ 𝑙 ≤𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞,0, |𝜎𝑞|) ⊧ 𝑄).

Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎 ⊧ 𝑝, if (𝜎,0, |𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable 
if 𝜎 ⊧ 𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎 ⊧ 𝑝 for all 𝜎.

Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤
def
= 𝑃 ∨ ¬𝑃 and ⊥

def
= 𝑃 ∧ ¬𝑃 , for any 

formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.

2.3. Normal form

Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL 
formula 𝑄. Then, the NF can be defined as follows:

Definition 1. Normal Form of 𝑄:

𝑁𝐹 (𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) ∨ ∨𝑛

𝑖=1(𝑄𝑐𝑖 ∧○𝑄′
𝑖
)

To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟

𝑖=1(𝑄𝑖 ∧○𝑄′
𝑖
) to replace 

∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧○𝑄′

𝑖
). Thus,

𝑁𝐹 (𝑄) ≡𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧○𝑄′

𝑖
)

where 𝑄𝑒 and 𝑄𝑖 are state formulas.

Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.

The proof of this theorem can be found in [26].

Example 1. Given a PPTL formula 𝑓 , 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get

𝑁𝐹 (𝑓 ) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧○⊤) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; (𝑞;⊤)))

3. Principle of SAT-based bounded model checking with PPTL

In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we 
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of 
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and 
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only 
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖

. In the following, we define the bounded semantics of PPTL formulas. 
Let 𝜎 be an interval and 𝑃 a PPTL formula.



Theoretical Computer Science 1049 (2025) 115368

5

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 3. 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝. 

3.1. Bounded semantics

In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.

Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼, 𝑇 ,𝐿) where 𝑆 is the set of sates, 𝐼 ⊆ 𝑆 is the set of initial states, 
𝑇 ⊆ 𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.

We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can 
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite. 
Therefore, in the following, we give the definition of 𝑘− 𝑙𝑜𝑜𝑝 in an interval.

Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,… , 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,… , 𝑠𝑘⟩𝜔, we call 
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.

Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈𝑁0. Now we can define the successor of state 
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:

𝑠𝑢𝑐𝑐(𝑖) =
⎧⎪⎨⎪⎩

𝑖+ 1 if 𝑖 < 𝑘

𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝

𝑘+ 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval 

With bounded model checking of PPTL, given a bound 𝑘 ∈𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an 
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval 
< 𝑠𝑖,… , 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to 
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .

The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition

(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘

(𝜎, 𝑖) ⊧𝑘

𝜖

iff 𝑖 < 𝑘

A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎,0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have 
𝜎 ⊧𝑘 𝑃 iff (𝜎,0, 𝑘) ⊧ 𝑃 .

As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics 
of PPTL is sound.

3.2. Bounded model checking

According to the structure of interval 𝜎, two basic lemmas are given below:

Lemma 1. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓 .

Proof. To prove Lemma 1, we first prove a stronger conclusion given below:

(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)

Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓 :

Base case:

𝑓 ≡ 𝑝 ∈ 𝑃𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖, |𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑝.



Theoretical Computer Science 1049 (2025) 115368

6

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 4. 𝜎 is a finite interval. 

Inductive cases:

1. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Then, we have, (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 . Further, 
(𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 and (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 , leading to (𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 .

2. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Since 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝, so, 𝑠𝑢𝑐𝑐(𝑖) ≤ 𝑘 < |𝜎|. Then, by 
hypothesis, we have,

(𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 . By the definitions of semantics, (𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 ○𝑓

iff (𝜎, 𝑖, 𝑘) ⊧○𝑓 and (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖+ 1, |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 , so (𝜎, 𝑖, 𝑘) ⊧○𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 .

3. Suppose for any PPTL formulas 𝑓1 and 𝑓2, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 and (𝜎, 𝑖, 𝑘) ⊧ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓2. Then, by the 
definitions of bounded semantics and model semantics, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 ∨ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 ∨ 𝑓2. □

Note that we do not need to deal with 𝜀 and 𝜖

in the above inductive cases since 𝜀 ≡ ¬○⊤ and 𝜖

≡○⊤.

Lemma 2. Let f be a PPTL formula, and 𝜎 a finite interval (Fig. 4). Then 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 .

Proof. Since 𝜎 is a finite interval, so |𝜎| ∈𝑁0.

𝜎 ⊧ 𝑓 ⇔ (𝜎,0, |𝜎|) ⊧ 𝑓

⇔ (𝜎,0, 𝑘) ⊧ 𝑓 ∧ 𝑘 = |𝜎|
⇒ ∃𝑘,𝑘 ≥ 0, (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 □

Theorem 2. Suppose a system is described by a Kripke structure M, and some property is defined by a PPTL formula 𝑓 . Let 𝑀 be the set 
of all intervals generated in M. We define 𝑀 ⊧ ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 as well as 𝑀 ⊧𝑘 ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . Then we have 
𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 .

Proof. We need prove that ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 iff ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . To do so, we consider intervals in 𝑀 as infinite or finite ones 
respectively.

1. Suppose 𝜎 is infinite, there must be an integer 𝑘 ≥ 0 that makes 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝. By Lemma 1:

𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓

we have,

𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓

2. Suppose interval 𝜎 is finite, i.e., |𝜎| =𝑚 ∈𝑁0.

“ ⇒ ” ∶𝑀 ⊧ ∃𝑓 ⇔ ∃𝜎 ∈𝑀 ∧ 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,Σ ⊧𝑘 ∃𝑓 (Lemma 2)

“ ⇐ ” ∶ ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0, 𝑘) ⊧ 𝑓

Let 𝜎′ =< 𝑠0, 𝑠1,… , 𝑠𝑘 >, we have (𝜎′,0, 𝑘) ⊧ 𝑓 . Since 𝜎′ is a subinterval 

of 𝜎 and |𝜎′| = 𝑘, hence, ∃𝜎′ ∈𝑀 and 𝜎′ ⊧ 𝑓 , leading to 𝑀 ⊧ ∃𝑓.

As a result, ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇒𝑀 ⊧ ∃𝑓. □

3.3. Reducing bounded model checking with PPTL to SAT

Given a finite state transition system 𝑀 (a Kripke structure or NFG), the property of the system in terms of a PPTL formula 𝑓 , and 
a bound 𝑘, then the procedure of BMC can be described as a process for constructing a proposition formula [𝑀,𝑓 ]𝑘. Let ⟨𝑠0,… , 𝑠𝑘⟩ be 
a subinterval of interval 𝜎. The definition of formula [𝑀,𝑓 ]𝑘 consists of two components: 𝑀𝑘, the first component, is a propositional 
formula that constrains ⟨𝑠0,… , 𝑠𝑘⟩ to be a valid interval starting from an initial state; 𝑋𝑘 , the second component, a propositional 



Theoretical Computer Science 1049 (2025) 115368

7

Z. Duan, C. Tian, N. Zhang et al. 

formula that constrains 𝜎 to satisfy 𝑓 with bound 𝑘. To define the second component, we first give the definition of 𝑙𝑜𝑜𝑝 𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛, 
which is a propositional formula that is evaluated to true only if the interval 𝜎 contains a loop; then we give some translation rules 
for formulas.

Definition 4. For a Kripke structure M, and k ≥ 0,

𝑀𝑘

def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1)

Loop condition:

𝐿(𝑘,𝑙)
def 
= 𝑇 (𝑠𝑘, 𝑠𝑙)  (0 ≤ 𝑙 ≤ 𝑘)

𝐿𝑘

def 
= ∨𝑘

𝑙=0 𝐿(𝑘,𝑙)

Let 𝑝 be an atomic proposition, and 𝑓 , 𝑔 be PPTL formulas, 𝜎 an interval with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝, 𝑠𝑖 the current state, and 𝑘 the bound, 
where 0 ≤ 𝑖, 𝑙, 𝑘 ≤ |𝜎|, 𝑖, 𝑙 ≤ 𝑘. The translation of a PPTL formula is given below:

k-loop: Translation 𝑓 (𝑖, 𝑘, 𝑙) of a PPTL formula 𝑓 over an infinite interval 𝜎 with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 is inductively defined as follows.

𝑝(𝑖,𝑘,𝑙)
def 
= 𝑝(𝑠𝑖) if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition, meaning 𝑠𝑖[𝑝]

(¬𝑓 )(𝑖,𝑘,𝑙)
def 
= ¬𝑓(𝑖,𝑘,𝑙)

(𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙)

(○𝑓 )(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑠𝑢𝑐𝑐(𝑖),𝑘,𝑙)

𝜀(𝑖,𝑘,𝑙)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘,𝑙)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

For the translation presented above, a new propositional variable is introduced for each intermediate formula 𝑒(𝑖,𝑘,𝑙), where 𝑒 is a 
sub-formula of PPTL formula 𝑓 and 0 ≤ 𝑖 ≤ 𝑘 and 𝑙 indicates the existence of (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝. If 𝑒 is an atomic proposition or its negation, 
𝑒(𝑖,𝑘,𝑙) is substituted by a boolean variable with the truth-value at state 𝑠𝑖. Otherwise, 𝑒(𝑖,𝑘,𝑙) indicates a propositional formula whose 
satisfiability should be considered over the interval (𝑠𝑖,… , 𝑠𝑘).

no loop: Translation 𝑓 (𝑖, 𝑘) of a PPTL formula 𝑓 for a finite interval 𝜎 (with no loop).

𝑝(𝑖,𝑘)
def 
= 𝑝(𝑠𝑖)

(¬𝑓 )(𝑖,𝑘)
def 
= ¬𝑓(𝑖,𝑘)

(𝑓 ∨ 𝑔)(𝑖,𝑘)
def 
= 𝑓(𝑖,𝑘) ∨ 𝑔(𝑖,𝑘)

(○𝑓 )(𝑖,𝑘)
def 
= 𝑓(𝑖+1,𝑘)

𝑓(𝑘+1,𝑘)
def 
= ⊥

𝜀(𝑖,𝑘)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

When the intermediate formula 𝑒(𝑖,𝑘) appears in a PPTL formula for a finite interval (with no loop), the explanations are similar to 
the ones for a PPTL formula with an interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 and omitted here.

General translation (BMC to SAT): 

𝑋𝑘

def 
= (¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))

[𝑀,𝑓 ]𝑘
def 
= 𝑀𝑘 ∧𝑋𝑘

i.e.:

[𝑀,𝑓 ]𝑘
def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))]



Theoretical Computer Science 1049 (2025) 115368

8

Z. Duan, C. Tian, N. Zhang et al. 

As we can see, the right side of the definition can be divided into two parts: the first part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (¬𝐿𝑘 ∧ 𝑓(0,𝑘))

indicates an interval with no loop and the translation without loop is used; the second part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧
𝑓(0,𝑘,𝑙))) presents that an interval with a 𝑘 − 𝑙𝑜𝑜𝑝 and all possible starting points 𝑙 of a loop and the translation for a 𝑘 − 𝑙𝑜𝑜𝑝 is 
conjoined with the corresponding loop condition 𝐿(𝑘,𝑙).

Lemma 3. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 an interval. The translation 𝑓(𝑖,𝑘,𝑙) or 𝑓(𝑖,𝑘) is defined as above. Then

(1) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘,𝑙) if 𝜎 is infinite with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 or

(2) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘) if 𝜎 is finite.

Proof. We prove only (1) but in a stronger version. A similar proof can be given to prove (2). The proof proceeds by induction on 
the rules of the definition of translation. 
Base: for an atomic proposition 𝑝 ∈ 𝑃𝑟𝑜𝑝.

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ while (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙) iff 𝜎 ⊧𝑘 𝑝(𝑠𝑖) iff 𝑠𝑖[𝑝] = ⊤. So, (𝜎, 𝑖) ⊧𝑘 𝑝 iff (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙)
Induction: 
Suppose (𝜎, 𝑖) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙), (𝜎, 𝑖) ⊧𝑘 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙). We have,

1) (𝜎, 𝑖) ⊧𝑘 ¬𝑓 iff (𝜎, 𝑖) ̸⊧𝑘 𝑓 def

iff (𝜎, 𝑖) ̸⊧𝑘 𝑓(0,𝑘,𝑙) hypothesis 
iff (𝜎, 𝑖) ⊧𝑘 ¬𝑓(0,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (¬𝑓 )(0,𝑘,𝑙) def

2) (𝜎, 𝑖) ⊧𝑘 𝑓 ∨ 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑓 or (𝜎, 𝑖) ⊧𝑘 𝑔 def

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) or (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙) def

3) (𝜎, 𝑖) ⊧𝑘 ○𝑓 iff (𝜎, 𝑖) ⊧○𝑓 Lemma 1
iff (𝜎, 𝑖+ 1) ⊧ 𝑓 Def

iff (𝜎, 𝑖+ 1) ⊧ 𝑓(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧ (○𝑓 )(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (○𝑓 )(𝑖,𝑘,𝑙) Lemma 1

We do not need to consider 𝜀 and 𝜖
again here. When 𝑖 = 0 the Lemma 3 is proved. Now we come to prove an important conclusion 

formalized in Theorem 3.

Theorem 3. [𝑀,𝑓 ]𝑘 is satisfiable iff M ⊧𝑘 ∃ f.

Proof. ``⇒'': Suppose [𝑀,𝑓 ]𝑘 is satisfiable. That is, ∃𝑘 ≥ 0, 𝜎 ∈𝑀,𝜎 ⊧ [𝑀,𝑓 ]𝑘 ⇔ 𝜎 ⊧𝑀𝑘 ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))].

If |𝜎| = 𝜔 with (𝑘, 𝑙)-loop and 𝑙 ≤ 𝑘, we have,

𝜎 ⊧ [𝑀,𝑓 ]𝑘 ⇒ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙)) def of [𝑀,𝑓 ]𝑘

⇒ 𝜎 ⊧ ∃𝑗 0 ≤ 𝑗 ≤ 𝑘 𝑓(0,𝑘,𝑗)
⇒ 𝜎 ⊧ 𝑓(0,𝑘,𝑗) (0 ≤ 𝑗 ≤ 𝑘)
⇒ 𝜎 ⊧𝑘 𝑓(0,𝑘,𝑗) (0 ≤ 𝑗 ≤ 𝑘) Lemma 1
⇒ 𝜎 ⊧𝑘 𝑓 Lemma 3
⇒ ∃𝑘 𝑘 ≥ 0, 𝜎 ∈𝑀 𝜎 ⊧𝑘 𝑓

⇒ 𝑀 ⊧𝑘 ∃𝑓 def

If |𝜎| ∈𝑁0 with no loop, we have,

𝜎 ⊧ [𝑀,𝑓 ]𝑘 ⇒ 𝜎 ⊧ 𝑓(0,𝑘) def of [𝑀,𝑓 ]𝑘
⇒ ∃𝑘𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓(0,𝑘) Lemma 1
⇒ ∃𝑘𝑘 ≥ 0, 𝜎 ∈𝑀 𝜎 ⊧𝑘 𝑓 Lemma 3
⇒ 𝑀 ⊧𝑘 ∃𝑓 def

``⇐'': 
Suppose 𝑀 ⊧𝑘 ∃𝑓 . Since 𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝜎 ∈𝑀,𝜎 ⊧𝑘 𝑓 , so 𝑘 ≥ 0 is the bound, and there exists subinterval < 𝑠0, ..., 𝑠𝑘 > of 𝜎 ∈𝑀 such 
that 𝜎 ⊧𝑘 𝑀𝑘 ≡ 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1).
If |𝜎| = 𝜔 with (𝑘, 𝑙)-loop, there is a 𝑙,0 ≤ 𝑙 ≤ 𝑘 and 𝑇 (𝑠𝑘, 𝑠𝑙), so 𝜎 ⊧𝑘 𝑇 (𝑠𝑘, 𝑠𝑙).

𝜎 ⊧𝑘 𝑓 ⇒ 𝜎 ⊧𝑘 𝑓(0,𝑘,𝑙)) Lemma 3
⇒ 𝜎 ⊧𝑘 𝑀𝑘 ∧𝐿(𝑘, 𝑙) ∧ 𝑓(0,𝑘,𝑙)
⇒ 𝜎 ⊧𝑘 [𝑀,𝑓 ]𝑘 def of [𝑀,𝑓 ]𝑘

If |𝜎| = 𝜔 without loop, 𝜎 ⊧𝑘 ¬𝐿𝑘, leading to 𝜎 ⊧𝑘 𝑀𝑘 ∧ ¬𝐿𝑘. Thus, we have,



Theoretical Computer Science 1049 (2025) 115368

9

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 5. Execution of 𝑇 with RMS algorithm. 

Fig. 6. Execution of 𝑇𝑓 with RMS algorithm. 

Fig. 7. Kripke structure 𝑀 of 𝑇𝑓 with RMS algorithm. 

𝜎 ⊧𝑘 𝑓 ⇒ 𝜎 ⊧𝑘 𝑓(0,𝑘)) Lemma 3
⇒ 𝜎 ⊧𝑘 𝑀𝑘 ∧ ¬𝐿𝑘 ∧ 𝑓(0,𝑘)
⇒ 𝜎 ⊧𝑘 [𝑀,𝑓 ]𝑘 def of [𝑀,𝑓 ]𝑘 □

4. A case study

RMS (rate monotonic scheduling) is a classical algorithm for periodic task scheduling proposed by Liu and Layland in 1973 [29]. 
As one of the static priority-driven scheduling approaches, RMS is optimal. Let 𝑇 = {𝑡1, 𝑡2,⋯ , 𝑡𝑛} be a set consisting of 𝑛 periodic 
tasks. A task is defined as a quadruple 𝑡𝑖 = (𝑇𝑖,𝐷𝑖,𝐸𝑖, 𝑃𝑖). 𝑇𝑖 is the period of 𝑡𝑖, 𝐷𝑖 is the deadline of 𝑡�
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn0file2 in your response to cite this file, or to surface it as a link.






























Bounded Model Checking

Armin Biere1 Alessandro Cimatti2 Edmund M. Clarke3

Ofer Strichman3 Yunshan Zhu4 ?

1 Institute of Computer Systems, ETH Zurich, 8092 Zurich, Switzerland.
Email: biere@inf.ethz.ch

2 Istituto per la Ricerca Scientifica e Technologica (IRST)
via Sommarive 18, 38055 Povo (TN), Italy. Email: cimatti@irst.itc.it

3 Computer Science Department, Carnegie Mellon University, 5000 Forbes Avenue, Pittsburgh,
PA 15213, USA. Email: {emc,ofers}@cs.cmu.edu

4 ATG, Synopsys, Inc., 700 East Middlefield Road, Mountain View, CA 94043, USA.
Email: yunshan@synopsys.com

Vol. 58 of Advances in Computers, 2003. Academic Press (pre-print).

Abstract. Symbolic model checking with Binary Decision Diagrams (BDDs)
has been successfully used in the last decade for formally verifying finite state
systems such as sequential circuits and protocols. Since its introduction in the
beginning of the 90’s, it has been integrated in the quality assurance process of
several major hardware companies. The main bottleneck of this method is that
BDDs may grow exponentially, and hence the amount of available memory re-
stricts the size of circuits that can be verified efficiently. In this article we survey
a technique called Bounded Model Checking (BMC), which uses a propositional
SAT solver rather than BDD manipulation techniques. Since its introduction in
1999, BMC has been well received by the industry. It can find many logical er-
rors in complex systems that can not be handled by competing techniques, and is
therefore widely perceived as a complementary technique to BDD-based model
checking. This observation is supported by several independent comparisons that
have been published in the last few years.

1 Introduction

Techniques for automatic formal verification of finite state transition systems have de-
veloped in the last 12 years to the point where major chip design companies are begin-
ning to integrate them in their normal quality assurance process. The most widely used
of these methods is called Model Checking[11, 13]. In model checking, the design to
be verified is modeled as a finite state machine, and the specification is formalized by
writing temporal logic properties. The reachable states of the design are then traversed

? This research was sponsored by the Semiconductor Research Corporation (SRC) under con-
tract no. 99-TJ-684, the National Science Foundation (NSF) under grant no. CCR-9803774, the
Army Research Office (ARO) under grant DAAD19-01-1-0485, the Office of Naval Research
(ONR), and the Naval Research Laboratory (NRL) under contract no. N00014-01-1-0796. The
views and conclusions contained in this document are those of the author and should not be in-
terpreted as representing the official policies, either expressed or implied, of SRC, ARO, NSF,
ONR, NRL, the U.S. government or any other entity.



in order to verify the properties. In case the property fails, a counterexample is gener-
ated in the form of a sequence of states. In general, properties are classified to ‘safety’
and ’liveness’ properties. While the former declares what should not happen (or equiv-
alently, what should always happen), the latter declares what should eventually happen.
A counterexample to safety properties is a trace of states, where the last state contra-
dicts the property. A counterexample to liveness properties, in its simplest form, is a
path to a loop that does not contain the desired state. Such a loop represents an infinite
path that never reaches the specified state.

It is impossible to know whether the specification of a system is correct or complete
– How can you know if what you wrote fully captures what you meant ? As a result,
there is no such thing as a ‘correct system’; it is only possible to check whether a system
satisfies its specification or not. Moreover, even the most advanced model checkers
are unable to verify all the desired properties of a system in a reasonable amount of
time, due to the immense state-spaces of such systems. Model checking is often used
for finding logical errors (‘falsification’) rather than for proving that they do not exist
(‘verification’). Users of model checking tools typically consider it as complimentary
to the more traditional methods of testing and simulation, and not as an alternative.
These tools are capable of finding errors that are not likely to be found by simulation.
The reason for this is that unlike simulators, which examine a relatively small set of
test cases, model checkers consider all possible behaviors or executions of the system.
Also, the process of writing the temporal properties in a formal language can be very
beneficial by itself, as it clarifies potential ambiguities in the specification.

The term Model Checking was coined by Clarke and Emerson [11] in the early
eighties. The first model checking algorithms explicitly enumerated the reachable states
of the system in order to check the correctness of a given specification. This restricted
the capacity of model checkers to systems with a few million states. Since the num-
ber of states can grow exponentially in the number of variables, early implementations
were only able to handle small designs and did not scale to examples with industrial
complexity.

It was the introduction of symbolic model checking [9, 15] that made the first break-
through towards wide usage of these techniques. In symbolic model checking, sets of
states are represented implicitly using Boolean functions. For example, assume that
the behavior of some system is determined by the two variables v1 and v2, and that
(11,01,10) are the three combinations of values that can be assigned to these variables
in any execution of this system. Rather than keeping and manipulating this explicit
list of states (as was done in explicit model checking), it is more efficient to handle a
Boolean function that represents this set, e.g. v1 ∨ v2. Manipulating Boolean formulas
can be done efficiently with Reduced Ordered Binary Decision Diagrams [8] (ROBDD,
or BDD for short), a compact, canonical graph representation of Boolean functions. The
process works roughly as follows1: The set of initial states is represented as a BDD. The
procedure then starts an iterative process, where at each step i, the set of states that can

1 The exact details of this procedure depends on the property that is being verified. Here we de-
scribe the procedure for testing simple ‘invariant’ properties, which state that some proposition
p has to hold invariantly in all reachable states. There is more than one way to perform this
check.



first be reached in i steps from an initial state are added to the BDD. At each such step,
the set of new states is intersected with the set of states that satisfy the negation of the
property. If the resulting set is non-empty, it means that an error has been detected. This
process terminates when the set of newly added states is empty or a an error is found.
The first case indicates that the property holds, because no reachable state contradicts
it. In the latter case, the model checker prints a counterexample. Note that termination
is guaranteed, since there are only finitely many states.

The combination of symbolic model checking with BDDs [20, 15], pushed the bar-
rier to systems with 1020 states and more [9]. Combining certain, mostly manual, ab-
straction techniques into this process pushed the bound even further. For the first time
a significant number of realistic systems could be verified, which resulted in a gradual
adoption of these procedures to the industry. Companies like Intel and IBM started de-
veloping their own in-house model checkers, first as experimental projects, and later as
one more component in their overall quality verification process of their chip designs.
Intel has invested significantly in this technology especially after the famous Pentium
bug a few years ago.

The bottleneck of these methods is the amount of memory that is required for stor-
ing and manipulating BDDs. The Boolean functions required to represent the set of
states can grow exponentially. Although numerous techniques such as decomposition,
abstraction and various reductions have been proposed through the years to tackle this
problem, full verification of many designs is still beyond the capacity of BDD based
symbolic model checkers.

The technique that we describe in this article, called Bounded Model Checking
(BMC), was first proposed by Biere et al. in 1999 [4]. It does not solve the complexity
problem of model checking, since it still relies on an exponential procedure and hence
is limited in its capacity. But experiments have shown that it can solve many cases that
cannot be solved by BDD-based techniques. The converse is also true: there are prob-
lems that are better solved by BDD-based techniques. BMC also has the disadvantage
of not being able to prove the absence of errors, in most realistic cases, as we will later
explain. Therefore BMC joins the arsenal of automatic verification tools but does not
replace any of them.

The basic idea in BMC is to search for a counterexample in executions whose length
is bounded by some integer k. If no bug is found then one increases k until either a bug
is found, the problem becomes intractable, or some pre-known upper bound is reached
(this bound is called the Completeness Threshold of the design. We will elaborate on
this point in section 5). The BMC problem can be efficiently reduced to a propositional
satisfiability problem, and can therefore be solved by SAT methods rather than BDDs.
SAT procedures do not suffer from the space explosion problem of BDD-based meth-
ods. Modern SAT solvers can handle propositional satisfiability problems with hundreds
of thousands of variables or more.

Thus, although BMC aims at solving the same problem as traditional BDD-based
symbolic model checking, it has two unique characteristics: first, the user has to pro-
vide a bound on the number of cycles that should be explored, which implies that the
method is incomplete if the bound is not high enough. Second, it uses SAT techniques
rather than BDDs. Experiments with this idea showed that if k is small enough (typi-



cally not more than 60 to 80 cycles, depending on the model itself and the SAT solver),
it outperforms BDD-based techniques. Also, experiments have shown that there is little
correlation between what problems are hard for SAT and what problems are hard for
BDD based techniques. Therefore, the classes of problems that are known to be hard for
BDDs, can many times be solved with SAT. If the SAT checkers are tuned to take advan-
tage of the unique structure of the formulas resulting from BMC, this method improves
even further [27]. A research published by Intel [14] showed that BMC has advantages
in both capacity and productivity over BDD-based symbolic model checkers, when ap-
plied to typical designs taken from Pentium-4™. The improved productivity results
from the fact that normally BDD based techniques need more manual guidance in order
to optimize their performance. These and other published results with similar conclu-
sions led most relevant companies, only three years after the introduction of BMC, to
adopt it as a complementary technique to BDD-based symbolic model checking.

The rest of the article is structured as follows. In the next section we give a technical
introduction to model checking and to the temporal logic that is used for expressing the
properties. In section 3 we describe the bounded model checking problem. In the fol-
lowing section we describe the reduction of the BMC problem to Boolean satisfiability,
including a detailed example. In section 5 we describe several methods for achieving
completeness with BMC. In section 6 we describe some of the essential techniques un-
derlying modern SAT solvers, and in section 7 we quote several experiments carried out
by different groups, both from academia and industry, that compare these techniques to
state of the art BDD-based techniques. We survey related work and detail our conclu-
sions from the experiments in section 8.

2 Model checking

Model checking as a verification technique has three fundamental features. First, it is
automatic; It does not rely on complicated interaction with the user for incremental
property proving. If a property does not hold, the model checker generates a coun-
terexample trace automatically. Second, the systems being checked are assumed to be
finite2. Typical examples of finite systems, for which model checking has successfully
been applied, are digital sequential circuits and communication protocols. Finally, tem-
poral logic is used for specifying the system properties. Thus, model checking can be
summarized as an algorithmic technique for checking temporal properties of finite sys-
tems.

As the reader may have deduced from the terminology we used in the introduction,
we do not distinguish between the terms design, system, and model. An engineer work-
ing on real designs has to use a syntactic representation in a programming or hardware
description language. Since we are only considering finite systems, the semantics of the
engineer’s design is usually some sort of a finite automaton. Independent of the con-
crete design language, this finite automaton can be represented by a Kripke structure,

2 There is an ongoing interest in generalizing model checking algorithms to infinite systems, for
example, by including real-time, or using abstraction techniques. In this article we will restrict
the discussion to finite systems.



which is the standard representation of models in the model checking literature. It has
its origin in modal logics, the generalization of temporal logics.

Formally, a Kripke structure M is a quadruple M = (S, I,T,L) where S is the set of
states, I⊆ S is the set of initial states, T ⊆ S×S is the transition relation and L:S→P(A)
is the labeling function, where A is the set of atomic propositions, and P(A) denotes the
powerset over A. Labeling is a way to attach observations to the system: for a state s∈ S
the set L(s) is made of the atomic propositions that hold in s.

The notion of a Kripke structure is only a vehicle for illustrating the algorithms.
It captures the semantics of the system under investigation. For a concrete design lan-
guage, the process of extracting a Kripke structure from a given syntactic representation
may not be that easy. In particular, the size of the system description and the size of the
state space can be very different. For example, if we model a sequential circuit with
a netlist of gates and flip-flops then the state space can be exponentially larger than
the system description. A circuit implementing an n-bit counter illustrates this ratio: it
can easily be implemented with O(n) gates and O(n) flip-flops, though the state space
of this counter is 2n. The exponential growth in the number of states poses the main
challenge to model checking. This is also known as the state explosion problem.

The next step is to define the sequential behavior of a Kripke structure M. For this
purpose we use paths. Each path π in M is a sequence π = (s0,s1, . . .) of states, given
in an order that respects the transition relation of M. That is, T (si,si+1) for all 0 ≤ i <
|π| − 1. If I(s0), i.e., s0 is an initial state, then we say that the path is initialized. The
length |π| of π can either be finite or infinite. Note that in general some of the states
may not be reachable, i.e., no initialized path leads to them. For i < |π| we denote by
π(i) the i-th state si in the sequence and by πi = (si,si+1, . . .) the suffix of π starting with
state si. To simplify some technical arguments we assume that the set of initial states is
non-empty. For the same reason we assume that the transition relation is total, i.e., each
state has a successor state: for all s ∈ S there exists t ∈ S with T (s, t).

As an example, consider the mutual exclusion problem of two processes competing
for a shared resource. Pseudo code for this example can be found in Fig. 1. We assume
that the processes are executed on a single computing unit in an interleaved manner. The
wait statement puts a process into sleep. When all processes are asleep the scheduler
tries to find a waiting condition which holds and reactivates the corresponding process.
If all the waiting conditions are false the system stalls.

process A
forever

A.pc = 0 wait for B.pc = 0
A.pc = 1 access shared resource

end forever
end process

process B
forever

B.pc = 0 wait for A.pc = 0
B.pc = 1 access shared resource

end forever
end process

Fig. 1. Pseudo code for two processes A and B competing for a shared resource.

On an abstract level, each process has two program counter positions 0 and 1 with 1
representing the critical section. A process may only access the shared resource in the



critical section of its program. A state of the system is a pair of program counters and
can be encoded as a binary vector s ∈ S = {0,1}2 of length two. Thus S = {0,1}2 is the
set of states of the system. We assume that both processes start at program counter posi-
tion 0, which implies that the set of initial states I consists of the single state represented
by the Boolean vector 00. The transition relation consists of several possible transitions,
according to the following two rules: the next state s′ is the initial state 00 unless the
current state is already the initial state; The initial state can transition forth and back to
both 01 and 10. Thus, the transition relation T ⊆ S2 = {0,1}4 can be represented as the
following set of bit strings:

{0100,1000,1100,0001,0010}

A graphical representation of this example in form of a Kripke structure is shown in
Fig. 2. The initial state has an incoming edge without a source. The other edges corre-
spond to one of the five transitions. Note that unreachable states, such as state 11 in this
example, can only be removed after a reachability analysis has marked all reachable
states. Accordingly the sequence 11,00,10, . . . is a valid path of the Kripke structure,

00 1001

11

Fig. 2. A Kripke structure for two processes that preserve mutual exclusion.

but it is not initialized, since initialized paths start with the state 00. An example of
an initialized path is the sequence 00,01,00,10,00,01, . . . where each process takes its
turn to enter the critical region after the other process has left it.

Our example system is safe in the sense that the two processes obey the mutual
exclusion property: at most one process can be in its critical region. A negative formu-
lation of this property is that the state in which both processes are in their critical region
is not reachable. Thus a simple model checking algorithm to check safety properties is
to build the state transition graph and enumerate all reachable states through a graph
search, starting from the set of initial states. Each visited state is analyzed in order to
check whether it violates the safety property.

Now, assume that we add a faulty transition from 10 to 11. A depth first search,
starting from the initial state 00 visiting 10 and then reaching 11 will show that the bad
state 11 is reachable and thus the safety property fails. This path is a counterexample to
the safety property that can help the user to debug the system.

What we have discussed so far is a typical explicit model checking algorithm for
simple safety properties. It can be refined by building the Kripke structure on-the-fly:
only after a state of the system is visited for the first time, the set of transitions is
generated leaving this state. Once a bad state is found, the process terminates. This



technique is particularly useful if the number of reachable states is much smaller than
|S|, the number of all states, which is often the case in practice.

Recall that safety properties describe invariants of a system, that is, that something
bad does not happen. As we have seen, these properties can be checked by reachability
analysis, i.e. by searching through the states graph and checking that each visited state
does not violate the invariant. Also recall that in addition to safety properties, it is some-
times desirable to use liveness properties in order to check whether something good will
eventually happen. In the mutual exclusion example, a natural question would be to ask
whether each process will eventually enter its critical region. For the first process this
means that the state 01 is eventually reached. More complicated liveness properties can
specify repeatedly inevitable behavior, such as ‘a request always has to be acknowl-
edged’. To capture this nesting and mutual dependency of properties, temporal logic is
used as a specification language.

Temporal logic is an extension of classical logic. In this article we concentrate on
Propositional Linear Temporal Logic (PLTL, or LTL for short) as an extension of propo-
sitional logic. From propositional logic LTL inherits Boolean variables and Boolean op-
erators such as negation ¬, conjunction ∧, implication→ etc. In addition to the Boolean
connectives, LTL has temporal operators. First, there is the next time operator X. The
formula Xp specifies that property p holds at the next time step.

In Fig. 3(a) a path is shown for which Xp holds. Each state is labeled with the atomic
properties that hold in it. Fig. 3(b) depicts a path for which Xp does not hold, because p
holds in the first state but not in the next, second state. Now we can use this operator to

p p
...

p p p
...

(a) (b)

Fig. 3. Validity of next time operator in the formula Xp along a path.

build larger temporal formulas. For instance p∧X¬p holds iff p holds in the first state
and p does not hold in the second. As usual ¬ is the Boolean negation operator. This
formula is true for the path on Fig. 3(b) and fails for the path on Fig. 3(a). By nesting the
operator X we can specify the behavior of the system up to a certain depth. For instance
the formula XXp holds for both paths.

The next class of temporal operators that we discuss, allows specifying repeated
unbounded behavior along an infinite path. The Globally operator G is used for safety
properties. A formula Gp holds along a path if p holds in all states of the path. Thus,
it fails for the path in Fig. 3(b), since p does not hold in the second state. The safety
property for our earlier example, the Kripke structure of Fig. 2, can be specified as
G¬(c1∧c2), where ci labels the states where process i is in its critical section. It literally
can be translated into English as follows: for all states it is not the case that both c1 and
c2 are true.

If all initialized paths of a Kripke structure satisfy a property, we say that the prop-
erty holds for the Kripke structure. For instance by making the state 11 in Fig. 2 an



initial state, each path starting at 11 would be initialized and would violate G¬(c1∧c2)
already in its first state. However since in our model 11 is not an initial state the property
holds for the Kripke structure.

Finally we look at liveness properties. The simplest liveness operator is F, the Fi-
nally operator. The formula Fp holds along a path if p holds somewhere on the path.
Equivalently, it fails to hold if p stays unsatisfied along the whole path. For instance
Fp trivially holds in both paths of Fig. 3 since p is already satisfied in the first state.
Similarly F¬p holds for the path in Fig. 3(b), because p does not hold in the second
state.

The liveness property for Fig. 2, which says that the first process will eventually
reach its critical section, can be formalized as Fc1. Since the system may loop between
the initial state and the state 10 on the right, never reaching 01, this property does not
hold. The initialized infinite path that starts with 00 and then alternates between 00 and
10 is a counterexample.

Now we can start to build more sophisticated specifications. The request / acknowl-
edge property mentioned above is formulated as G(r → Fa), where r and a are atomic
propositions labeling states where a request and an acknowledge occurs, respectively.
The same idea can be used to specify that a certain sequence of actions a1,a2,a3 has
to follow a guard g: G(g → F(a1∧F(a2∧Fa3))). Note that there may be an arbitrary,
finite time interval (possibly empty) between the actions.

In this informal introduction to temporal logic, we will avoid a detailed explanation
of the binary temporal operators Until (U) and Release (R). The reader is referred to
[13] for more details. Also note that in the literature one can find an alternative notation
for temporal operators, such as dp for Xp, 3p for Fp and 2p for Gp.

The formal semantics of temporal formulas is defined with respect to paths of a
Kripke structure. Let π be an infinite path of a Kripke structure M and let f be a temporal
formula. We define recursively when f holds on π, written π |= f :

π |= p iff p ∈ L(π(0))

π |= ¬ f iff π 6|= f

π |= f ∧g iff π |= f and π |= g

π |= X f iff π1 |= f

π |= G f iff πi |= f for all i≥ 0

π |= F f iff πi |= f for some i≥ 0

π |= f Ug iff πi |= g for some i≥ 0 and π j |= f for all 0≤ j < i

π |= f Rg iff πi |= g if for all j < i, π j 6|= f

The semantics of the other Boolean operators such as disjunction and implication can be
inferred from the above definition. As mentioned above we say that a temporal formula
f holds for a Kripke structure M, written M |= f , iff π |= f for all initialized paths π of
M. Finally, we say that two temporal formulas f and g are equivalent, written f ≡ g iff
M |= f ↔M |= g for all Kripke structures M. With this notion, the semantics imply that
¬F¬p ≡Gp. Thus, F and G are dual operators.



The standard technique for model checking LTL [19] is to compute the product
of the Kripke structure with an automaton that represents the negation of the property
(this automaton captures exactly the execution sequences that violate the LTL formula).
Emptiness of the product automaton is an evidence of the correctness of the property.
More details about this procedure can be found in [13].

3 Bounded model checking

The original motivation of bounded model checking was to leverage the success of
SAT in solving Boolean formulas to model checking. During the last few years there
has been a tremendous increase in reasoning power of SAT solvers. They can now
handle instances with hundreds of thousands of variables and millions of clauses (we
will elaborate more on how these solvers work in section 6). Symbolic model checkers
with BDDs, on the other hand, can check systems with no more than a few hundred
latches. Though clearly the number of latches and the number of variables cannot be
compared directly, it seemed plausible that solving model checking with SAT could
benefit the former.

A similar approach has been taken in tackling the planning problem in Artificial
Intelligence [18]. Classical planning problems seek for a plan, i.e., a sequence of steps,
to perform some task (e.g. position cubes one above the other in descending size under
certain constraints on the intermediate states). As in BMC, the search for a plan is
restricted to paths with some predetermined bound. The possible plans in a given bound
are described by a SAT instance, which is polynomial in the original planning problem
and the bound. Compared to model checking, deterministic planning is only concerned
with simple safety properties: whether and how the goal state can be reached. In model
checking we want to check liveness properties and nested temporal properties as well.

Since LTL formulas are defined over all paths, finding counterexamples corresponds
to the question whether there exists a trace that contradicts them. If we find such a
trace, we call it a witness for the property. For example, a counterexample to M |=
Gp corresponds to the question whether there exists a witness to F¬p. For clarity of
presentation we will use path quantifiers E and A to denote whether the LTL formula is
expected to be correct over all paths or only over some path. In other words, M |= A f
means that M satisfies f over all initialized paths, and M |= E f means that there exists
an initialized path in M that satisfies f . We will assume that the formula is given in
negation normal form (NNF), in which negations are only allowed to occur in front of
atomic propositions. Every LTL formula can be transformed to this form by using the
duality of LTL operators and De-Morgan’s laws.

The basic idea of bounded model checking, as was explained before, is to consider
only a finite prefix of a path that may be a witness to an existential model checking prob-
lem. We restrict the length of the prefix by some bound k. In practice, we progressively
increase the bound, looking for witnesses in longer and longer traces.

A crucial observation is that, though the prefix of a path is finite, it still might rep-
resent an infinite path if there is a back loop from the last state of the prefix to any of
the previous states, as in Fig. 4(b). If there is no such back loop, as in Fig. 4(a), then
the prefix does not say anything about the infinite behavior of the path beyond state sk.



For instance, only a prefix with a back loop can represent a witness for Gp. Even if p
holds along all the states from s0 to sk, but there is no back loop from sk to a previous
state, we cannot conclude that we have found a witness for Gp, since p might not hold
at sk+1.

SkSi SkSiSl

(a) no loop (b) (k, l)-loop

Fig. 4. The two cases for a bounded path.

Definition 1. For l ≤ k we call a path π a (k, l)-loop if T (π(k),π(l)) and π = u · vω

with u = (π(0), . . . ,π(l−1)) and v = (π(l), . . . ,π(k))3. We call π a k-loop if there exists
k ≥ l ≥ 0 for which π is a (k, l)-loop.

We will use the notion of k-loops in order to define the bounded semantics of model
checking, i.e., semantics of model checking under bounded traces. The bounded seman-
tics is an approximation to the unbounded semantics, which will allow us to define the
bounded model checking problem. In the next section we will give a translation of a
bounded model checking problem into a satisfiability problem.

In the bounded semantics we only consider a finite prefix of a path. In particular,
we only use the first k + 1 states (s0, . . . ,sk) of a path to determine the validity of a
formula along that path. If a path is a k-loop then we simply maintain the original LTL
semantics, since all the information about this (infinite) path is contained in the prefix
of length k.

Definition 2 (Bounded Semantics for a Loop). Let k ≥ 0 and π be a k-loop. Then an
LTL formula f is valid along the path π with bound k (in symbols π |=k f ) iff π |= f .

We now consider the case where π is not a k-loop. The formula f := Fp is valid
along π in the unbounded semantics if we can find an index i ≥ 0 such that p is valid
along the suffix πi of π. In the bounded semantics the (k + 1)-th state π(k) does not
have a successor. Therefore, unlike the unbounded case, we cannot define the bounded
semantics recursively over suffixes (e.g. πi) of π. We therefore introduce the notation
π |=i

k f , where i is the current position in the prefix of π, which means that the suffix πi

of π satisfies f , i.e., π |=i
k f implies πi |= f .

Definition 3 (Bounded Semantics without a Loop). Let k ≥ 0, and let π be a path
that is not a k-loop. Then an LTL formula f is valid along π with bound k (in symbols

3 The notation vω represents an infinite repetition of v.



π |=k f ) iff π |=0
k f where

π |=i
k p iff p ∈ L(π(i))

π |=i
k ¬p iff p 6∈ L(π(i))

π |=i
k f ∧g iff π |=i

k f and π |=i
k g

π |=i
k f ∨g iff π |=i

k f or π |=i
k g

π |=i
k G f is always false

π |=i
k F f iff ∃ j, i≤ j ≤ k. π |= j

k f

π |=i
k X f iff i < k and π |=i+1

k f

π |=i
k f Ug iff ∃ j, i≤ j ≤ k. π |= j

k g and ∀n, i≤ n < j. π |=n
k f

π |=i
k f Rg iff ∃ j, i≤ j ≤ k. π |= j

k f and ∀n, i≤ n < j. π |=n
k g

Note that if π is not a k-loop, then we say that G f is not valid along π in the bounded
semantics with bound k since f might not hold along πk+1. These constraints imply that
for the bounded semantics the duality between G and F (¬F f ≡G¬ f ) no longer holds.

Now we describe how the existential model checking problem (M |= E f ) can be
reduced to a bounded existential model checking problem (M |=k E f ). The basis for
this reduction lies in the following two lemmas.

Lemma 1. Let f be an LTL formula and π a path, then π |=k f ⇒ π |= f

Lemma 2. Let f be an LTL formula and M a Kripke structure. If M |= E f then there
exists k ≥ 0 with M |=k E f

Based on lemmas 1 and 2, we can now state the main theorem of this section. Infor-
mally, Theorem 1 says that if we take a sufficiently high bound, then the bounded and
unbounded semantics are equivalent.

Theorem 1. Let f be an LTL formula and M be a Kripke structure. Then M |= E f iff
there exists k ≥ 0 s.t. M |=k E f .

4 Reducing bounded model checking to SAT

In the previous section we defined the semantics for bounded model checking. We now
show how to reduce bounded model checking to propositional satisfiability. This reduc-
tion enables us to use efficient propositional SAT solvers to perform model checking.

Given a Kripke structure M, an LTL formula f and a bound k, we will construct a
propositional formula [[ M, f ]]k. Let s0, . . . ,sk be a finite sequence of states on a path π.
Each si represents a state at time step i and consists of an assignment of truth values to
the set of state variables. The formula [[ M, f ]]k encodes constraints on s0, . . . ,sk such
that [[ M, f ]]k is satisfiable iff π is a witness for f . The definition of formula [[ M, f ]]k
will be presented as three separate components. We first define a propositional formula
[[ M ]]k that constrains s0, . . . ,sk to be a valid path starting from an initial state. We then



define the loop condition, which is a propositional formula that is evaluated to true only
if the path π contains a loop. Finally, we define a propositional formula that constrains
π to satisfy f .

Definition 4 (Unfolding of the Transition Relation). For a Kripke structure M, k ≥ 0

[[ M ]]k := I(s0)∧
k−1∧
i=0

T (si,si+1)

The translation of an LTL formula depends on the shape of the path π. We define the
propositional formula lLk to be true if and only if there is a transition from state sk to
state sl . By definition, lLk is equal to T (sk,sl). We use lLk to define the loop condition
Lk:

Definition 5 (Loop Condition). The loop condition Lk is true if and only if there exists
a back loop from state sk to a previous state or to itself: Lk :=

∨k
l=0 lLk

Depending on whether a path is a k-loop (see Fig. 4), we have two different trans-
lations of a temporal formula f . First we consider the case where the path is a k-loop.
We give a recursive translation of an LTL formula f for a k-loop path π. The transla-
tion of f recurses over its subterms and the states in π. The intermediate formula l [[ · ]]

i
k

depends on three parameters: l, k and i. We use l for the start position of the loop, k for
the bound, and i for the current position in π.

Definition 6 (Successor in a Loop). Let k, l and i be non-negative integers s.t. l, i ≤
k. Define the successor succ(i) of i in a (k, l)-loop as succ(i) := i + 1 for i < k and
succ(i) := l for i = k.

Definition 7 (Translation of an LTL Formula for a Loop). Let f be an LTL formula,
k, l, i≥ 0, with l, i≤ k.

l [[ p ]]ik := p(si) l [[ G f ]]ik := l [[ f ]]ik ∧ l [[ G f ]]succ(i)
k

l [[ ¬p ]]ik := ¬p(si) l [[ F f ]]ik := l [[ f ]]ik ∨ l [[ F f ]]succ(i)
k

l [[ f ∨g ]]ik := l [[ f ]]ik ∨ l [[ g ]]ik l [[ f Ug ]]ik := l [[ g ]]ik ∨ (l [[ f ]]ik ∧ l [[ f Ug ]]succ(i)
k )

l [[ f ∧g ]]ik := l [[ f ]]ik ∧ l [[ g ]]ik l [[ f Rg ]]ik := l [[ g ]]ik ∧ (l [[ f ]]ik ∨ l [[ f Rg ]]succ(i)
k )

l [[ X f ]]ik := l [[ f ]]succ(i)
k

The translation in Definition 7 is linear with respect to the size of f and bound
k if subterms are shared. A common technique for sharing subterms in propositional
logic is to introduce new Boolean variables for subterms. Consider, for example, the
formula (a∧ b)∨ (c → (a∧ b)). We introduce a new variable x for the subterm a∧ b,
and transform the original formula into (x∨(c→ x))∧(x↔ (a∧b)). The transformation
clearly preserves satisfiability.

For the translation presented in Definition 7, a new propositional variable is intro-
duced for each intermediate formula l [[ h ]]ik, where h is a subterm of the LTL formula



f and i ranges from 0 to k. The total number of new variables is O(| f |× k), where | f |
denotes the size of f . The size of the propositional formula l [[ f ]]0k is also O(| f |× k).

For the case where π is not a k-loop, the translation can be treated as a special case of
the k-loop translation. For Kripke structures with total transition relations, every finite
path π can be extended to an infinite one. Since the property of the path beyond state sk

is unknown, we make a conservative approximation and assume all properties beyond
sk are false.

Definition 8 (Translation of an LTL Formula without a Loop).
Inductive Case: ∀i≤ k

[[ p ]]ik := p(si) [[ G f ]]ik := [[ f ]]ik ∧ [[ G f ]]i+1
k

[[ ¬p ]]ik := ¬p(si) [[ F f ]]ik := [[ f ]]ik ∨ [[ F f ]]i+1
k

[[ f ∨g ]]ik := [[ f ]]ik ∨ [[ g ]]ik [[ f Ug ]]ik := [[ g ]]ik ∨ ([[ f ]]ik ∧ [[ f Ug ]]i+1
k )

[[ f ∧g ]]ik := [[ f ]]ik ∧ [[ g ]]ik [[ f Rg ]]ik := [[ g ]]ik ∧ ([[ f ]]ik ∨ [[ f Rg ]]i+1
k )

[[ X f ]]ik := [[ f ]]i+1
k

Base Case:
[[ f ]]k+1

k := 0

Combining all components, the encoding of a bounded model checking problem in
propositional logic is defined as follows.

Definition 9 (General Translation). Let f be an LTL formula, M a Kripke structure
and k ≥ 0

[[ M, f ]]k := [[ M ]]k ∧

((
¬Lk ∧ [[ f ]]0k

)
∨

k∨
l=0

(
lLk ∧ l [[ f ]]0k

))

The left side of the disjunction is the case where there is no back loop and the
translation without a loop is used. The right side represent all possible starting points l
of a loop, and the translation for a (k, l)-loop is conjoined with the corresponding lLk

loop condition. The size of [[ M, f ]]k is O(| f |× k×|M|), where |M| represents the size
of the syntactic description of the initial state I and the transition relation T .

The translation scheme guarantees the following theorem, which we state without
proof:

Theorem 2. [[ M, f ]]k is satisfiable iff M |=k E f .

Thus, the reduction of bounded model checking to SAT is sound and complete with
respect to the bounded semantics.

Example 1. Let us consider the mutual exclusion example in Fig. 2. Each state s of the
system M is represented by two bit variables. We use s[1] for the high bit and s[0] for
the low bit.



The initial state is represented as follows,

I(s) := ¬s[1]∧¬s[0]

The transition relation is represented as follows,

T (s,s′) :=(¬s[1]∧(s[0]↔¬s′[0]))∨(¬s[0]∧(s[1]↔¬s′[1]))∨(s[0]∧s[1]∧¬s′[1]∧¬s′[0])

We now add a faulty transition from state 10 to state 11. We denote by Tf the new
faulty transition relation.

Tf (s,s′) := T (s,s′)∨ (s[1]∧¬s[0]∧ s′[1]∧ s′[0])

Consider the safety property that at most one process can be in the critical region
at any time. The property can be represented as G¬p, where p is s[1]∧ s[0]. Using
BMC, we attempt to find a counterexample of the property, or, in other words, look for
a witness for Fp. The existence of such a witness indicates that the mutual exclusion
property is violated by M. If, on the other hand, no such witness can be found, it means
that this property holds up to the given bound.

Let us consider a case where the bound k = 2. Unrolling the transition relation
results in the following formula:

[[ M ]]2 := I(s0)∧Tf (s0,s1)∧Tf (s1,s2)

The loop condition is:

L2 :=
2∨

l=0

Tf (s2,sl)

The translation for paths without loops is:

[[ Fp ]]02 := p(s0)∨ [[ Fp ]]12 [[ Fp ]]12 := p(s1)∨ [[ Fp ]]22
[[ Fp ]]22 := p(s2)∨ [[ Fp ]]32 [[ Fp ]]32 := 0

We can introduce a new variable for each intermediate formula [[ Fp ]]i2. Alternatively,
we can substitute all intermediate terms and obtain the following formula.

[[ Fp ]]02 := p(s0)∨ p(s1)∨ p(s2)

The translation with loops can be done similarly. Putting everything together we get the
following Boolean formula
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn0file3 in your response to cite this file, or to surface it as a link.


































 

软件学报 ISSN 1000-9825, CODEN RUXUEW E-mail: jos@iscas.ac.cn 
Journal of Software,2012,23(7):16561668 [doi: 10.3724/SP.J.1001.2012.04089] http://www.jos.org.cn 
©中国科学院软件研究所版权所有. Tel/Fax: +86-10-62562563 

 

概率计算树逻辑的限界模型检测


 

周从华+,  刘志锋,  王昌达 

(江苏大学 计算机科学与通信工程学院,江苏 镇江  212013) 

Bounded Model Checking for Probabilistic Computation Tree Logic 

ZHOU Cong-Hua+,  LIU Zhi-Feng,  WANG Chang-Da 

(School of Computer Science and Telecommunication Engineering, Jiangsu University, Zhenjiang 212013, China) 

+ Corresponding author: E-mail: chzhou@ujs.edu.cn 

Zhou CH, Liu ZF, Wang CD. Bounded model checking for probabilistic computation tree logic. Journal of 

Software, 2012,23(7):16561668 (in Chinese). http://www.jos.org.cn/1000-9825/4089.htm 

Abstract:  In order to overcome the state explosion problem in model checking the probabilistic computation tree 

logic, a bounded model checking technique is proposed. First, the bounded semantics of the probabilistic 

computation tree logic is presented, and then its correctness is proved. Second, by a simple instance the criterion of 

the traditional termination, based on the length of path, is shown to fail. Based on the termination criterion used in 

the Newton iteration in numerical computing, a new criterion is given. Third, the bounded model checking 

procedure of the probabilistic computation tree logic is transformed into linear equations. Finally, three benchmarks 

are used to present the advantages of the bounded model checking. 

Key words: model checking; bounded model checking; probabilistic computation tree logic; Markov chains 

摘  要: 为了缓解概率计算树逻辑模型检测中的状态空间爆炸问题,提出了概率计算树逻辑的限界模型检测技

术.该技术首先定义概率计算树逻辑的限界语义,并证明其正确性;之后,通过实例说明在传统限界模型检测中,以路

径长度作为判断检测过程终止的标准已经失效,基于数值计算中牛顿迭代法的终止准则,设计了新的终止判断标准;

然后提出基于线性方程组求解的限界模型检测算法;最后,通过 3 个测试用例说明,概率计算树逻辑限界模型检测方

法在反例较短的情况下能够快速完成检测过程,而且比概率计算树逻辑的无界模型检测算法所需求得的状态空间

要少. 

关键词: 模型检测;限界模型检测;概率计算树逻辑;马尔可夫链 

中图法分类号: TP301   文献标识码: A 

模型检测[1,2]是一种有限状态系统验证技术,因其自动化程度高,逐渐引起了广泛的关注.目前,模型检测已

在计算机硬件、通信协议、安全协议的验证等方面获得了较大的成功.传统的模型检测技术利用计算树和线性

时态逻辑规约需要验证的属性,这两种时态逻辑可以规范系统行为的绝对正确性,如系统运行不可能失败.然而

实际上有很多随机现象,比如不可靠信道上的消息丢失,对这一类现象往往关心某种概率度量,如消息传送失败

                                                                 
 基金项目: 国家自然科学基金(61003288, 61111130184, 60773049); 江苏省自然科学基金(BK2010192); 教育部博士点基金

(20093227110005) 

 收稿时间:  2010-10-05; 定稿时间: 2011-07-08 



 

 

 

周从华 等:概率计算树逻辑的限界模型检测 1657 

 

的概率不高于 1%等等.对这类属性,计算树和线性时态逻辑是无法刻画的,因此,研究人员在计算树和线性时态

逻辑的基础上引入了概率算子,得到了概率计算树逻辑 PCTL[3]等规约形式,并提出了相应的概率模型检测 

方法[4,5]. 

概率模型检测一般以有限马尔可夫链作为系统的模型.与传统模型检测一样,状态空间爆炸问题(系统的规

模随着并发分量的增加呈指数级增长)[6,7]是概率模型检测实用化的主要瓶颈.为克服该问题,研究人员将传统

模型检测中的基于 OBDD 的符号化技术[810]、谓词抽象[11]、偏序归约[12]、对称归约[13]、组合推理[14]等状态

空间约简技术应用到了概率模型检测上,并获得了很好的效果.限界模型检测[1520]是近几年出现的一种新的空

间约简技术,它成功地缓解了计算树逻辑 CTL[1820]、线性时态逻辑 LTL[15]、时态认知逻辑 CTLK[17]在模型检

测过程中出现的状态空间爆炸问题.因此,将传统限界模型检测技术的思想应用到缓解概率计算树逻辑模型检

测中出现的状态空间爆炸问题,必将收到良好的效果,这也是本文主要的研究动机. 

限界模型检测的基本思想是,在有限的局部空间中逐步搜索属性成立的证据或者反例,从而达到约简状态

空间的目的.一般来讲,限界模型检测有 3 个核心问题,即限界语义的定义、检测过程终止的判别条件、限界模

型检测算法.本文围绕这 3 个问题对概率计算树逻辑 PCTL[3]的限界模型检测进行了系统的研究,具体工作包括

3 个方面:1) 将 PCTL 转换为概率约束仅为≥p 或者>p(p 表示事件发生的概率)形式的等价形式,定义了 PCTL

的限界语义,并证明了其正确性;2) 摒弃以路径长度作为终止标准的判别条件,基于数值计算中牛顿迭代法使

用的迭代过程终止标准,设计了新的检测过程终止判别条件.即,预先设置一个非常小的有理数,当相连两次限

界模型检测得到的概率度量的差控制在内时,检测过程终止;3) 设计了基于线性方程组求解的限界模型检测

算法,即将 PCTL 的限界模型检测问题转换为线性方程组的求解问题,从而可以借助于数值计算工具 matlab 完

成检测过程.另外,为了提高概率计算的精度,提出了两种 PCTL 限界模型检测过程终止判断标准的修正方案.实

验结果表明:1) 随着检测步长的增加,限界模型检测得到的概率度量越来越逼近真实的概率度量;2) PCTL 的限

界模型检测是一种前向搜索状态空间的方法,在属性为真的证据比较短的情况下,能够快速地验证属性,而且需

求的状态空间少于概率计算树逻辑的无界模型检测算法. 

1   相关工作 

传统限界模型检测技术有效地缓解了计算树逻辑 CTL、线性时态逻辑 LTL、时态认知逻辑 CTLK 在模型

检测过程中出现的状态空间爆炸问题.我们的研究不是对传统限界模型检测技术的简单推广,差别主要体现在

3 个方面:其一、传统限界模型检测以单一路径为分析对象,而我们的方法因为涉及到概率度量,因此将以路径

集合为分析对象.概率度量的计算,使得在定义限界语义时必须考虑路径集合的量化问题;其二、传统限界模型

检测通常预先给定一个路径的长度,以判断检测过程何时终止,我们通过一个通信协议说明这种方法不再适用

于 PCTL 的限界模型检测.为此,我们基于牛顿迭代方法中使用的计算过程终止判断标准,设计了一套完全不同

的判断检测过程终止的方法;其三、将 PCTL 限界模型检测问题转化为线性方程组的求解问题,而不是传统模型

检测方法中的命题公式满足性求解问题. 

据我们所知,目前还没有任何工作来探讨 PCTL 的限界模型检测问题.唯一与我们的工作比较接近的是

Penna 等学者在文献[21]中所做的工作.他们在 PCTL 的基础上提出了一种新的时态算子 Uk,得到一种新的时态

逻辑 BPCTL,然后针对 Uk 设计了一套算法.直观上,他们将 Uk 的解释限制在长度为 k 的路径上.与我们工作的主

要不同点在于,他们仍然在全局空间上设计Uk的模型检测算法,并能够直接计算出概率度量,因此本质上不是一

种限界模型检测方法.而我们的算法建立在局部空间上,是对真实概率度量的逐步逼近,这遵循限界模型检测的

思想. 

2   离散时间马尔可夫链与概率计算树逻辑 

离散时间马尔可夫链是一簇随机变量{X(k)|k=0,1,2,…},这里,X(k)是在每一个离散步的观察.X(k)的取值称

为状态,状态空间的集合是离散的.离散时间马尔可夫链必须满足马尔可夫性质,即 X(k)仅仅依赖于 X(k1),而与



 

 

 

1658 Journal of Software 软件学报 Vol.23, No.7, July 2012   

 

X(0),…,X(k2)无关.另外,我们考虑的离散时间马尔可夫链是齐次的,这意味着状态之间的转换概率独立于时

间.因此,给出状态之间的转换概率,就足够描述离散时间马尔可夫链. 

定义 1. 离散时间马尔可夫链 M=(S,P,sin,Ap,L)是一个五元组,这里, 

 S 是有限状态集; 

 P:SS[0,1]是转换概率函数,且满足对任意的状态 sS, ( , ) 1
s S

P s s


  ; 

 sinS 是初始状态; 

 Ap 是有限的原子命题集; 

 L:S2Ap 是标记函数. 

直觉上,一个离散时间马尔可夫链是一个所有转换关系附上离散概率的 Kripke 结构.在定义概率计算树

PCTL 的语法和语义之前,我们首先回顾一下概率论方面的基本内容.一项随机实验中,所有可能发生的结果形

成的集合称为样本空间,记为.集合2称为上的代数,当且仅当: 

 ; 

 如果 E,则\E; 

 如果 E1,E2,…,则
1

.i
i

E 
≥

 

概率空间是一个三元组 PS=(,,Pr),这里,为样本空间,集合为上的代数,Pr:[0,1]是度量函数,满 

足:1) Pr()=1;2) 对中两两不相交的序列 E1,E2,…,
1 1

( ) ( ).i ii i
Pr E Pr E

 

 
  称中任何元素是可度量的. 

定义 2(路径). 设 M 为离散时间马尔可夫链 ,M 中的路径是一个无穷状态序列 s0,s1,…,使得i≥0, 

P(si,si+1)>0. 

为表达方便起见,引入记号 Paths(s)表示从状态 s 出发的路径集合;对于路径=s0,s1,…,引入(i)表示上的

第 i 个状态 si.对于离散时间马尔可夫链 M 和状态 s,令=Paths(s),为代数,定义为={C()|sS*}.这里,C()= 

{|是的有限前缀}.上的概率度量 Prs 定义为 1 2 1
1 1

( ( , ,..., )) ( , ).s n i i
i n

Pr C s s s P s s 


 
≤ ≤

这里,s1=s.这样,我们从离散

时间马尔可夫链 M 和状态 s 演绎出了一个概率空间. 

概率计算树逻辑 PCTL是基于CTL的分支时态逻辑.PCTL由状态公式和路径公式组成,分别在马尔可夫链

的状态上解释状态公式,在路径上解释路径公式.PCTL 与 CTL 的主要区别在于去除了全称和存在路径量词,引

入了概率算子 PJ().这里,是路径公式,J 是[0,1]上的某个区间.PCTL 的形式化定义如下. 

定义 3(概率计算树逻辑 PCTL). 原子命题集 Ap 上的 PCTL 状态公式定义如下: 

::=true|a|12|12||PJ(). 

这里,aAp,是一条路径公式,J[0,1]是以有理数为边界的区间(选择有理数作为边界是为了方便计算机处理). 

PCTL 路径公式定义如下:::=X|F|G|1U2|1R2.这里,,1,2 是状态公式. 

为方便起见,不再显式地书写区间,而采用简写方式,例如 P≤0.5()表示 P[0,0.5](),P=1()表示 P[1,1]().PCTL

的满足性关系定义如下. 

定义 4(概率计算树逻辑 PCTL 的满足性关系). 令 aAp 为原子命题,M=(S,P,sin,Ap,L)是离散时间马尔可夫 

链,sS,1,2 是 PCTL 状态公式,是 PCTL 路径公式.对于状态公式满足性关系定义为: 

 sa 当且仅当 aL(s); 

 s1 当且仅当 s1; 

 s12 当且仅当 s1 且 s2; 

 s12 当且仅当 s1 或者 s2; 

 sPJ()当且仅当 Pr(s)J,这里,Pr(s)=Prs({Paths(s)|}). 

对于 M 中的路径,满足性关系定义为: 

 X1 当且仅当(1)1; 



 

 

 

周从华 等:概率计算树逻辑的限界模型检测 1659 

 

 F1 当且仅当存在自然数 i,使得(i)1; 

 G1 当且仅当对任意的自然数 i,(i)1; 

 1U2 当且仅当存在自然数 j,使得(j)2,且对任意小于 j 的自然数 i,(i)1; 

 1R2 当且仅当对任意自然数 j,(j)2;或者存在自然数 k,使得(k)1,且对任意不大于 k 的自然数

i,(i)2. 

3   PCTL 的限界模型检测 

3.1   PCTL的等价性 

限界模型检测的主要思想是在系统有限的局部空间中寻找属性成立的证据或者反例.对于 PCTL 中的计算

树逻辑部分,我们可以采用 CTL 限界模型检测中的技术来定义其限界语义.对于概率算子部分,限界语义必须保

证属性在有限局部空间中成立,在整个运行空间中也一定成立.对于 P≥p 这类算子,如果在有限局部空间中属性

成立的概率不小于实数 p,自然地,在整个运行空间上属性成立的概率也不小于 p.而对于P≤p这类算子,如果在有

限局部空间中属性成立的概率不大于实数 p,并不能保证在整个运行空间上属性成立的概率也不大于 p.为了保

证 P≤p 算子限界语义定义的正确性,本节我们探讨如何将 PCTL 公式转换为等价的且概率约束为≥p 或者>p 形

式的 PCTL 公式. 

定义 5(PCTL 公式的等价). 称 PCTL 状态公式,是等价的,记为,当且仅当对任意的离散时间马尔可 

夫链 M,任意的 sS,s当且仅当 s. 

不难验证我们有下面的等价关系: 

 P≤p(X)P≥1p(X);P<p(X)P>1p(X); 

 P≤p(F)P≥1p(G);P<p(F)P>1p(G); 

 P≤p(G)P≥1p(F);P<p(G)P>1p(F); 

 P≤p(U)P≥1p((U))P≥1p(R);P<p(U)P>1p((U))P>1p(R); 

 P≤p(R)P≥1p((R))P≥1p(U);P<p(R)P>1p((R))P>1p(U). 

上面的等价关系说明,可将≤(<)p 的概率约束转换为≥(>)p 的约束;下面的等价关系说明,可将否定算子直

接作用于原子命题上,且不会降低 PCTL 的表达力: 

 P≤p()P>p();P<p()P≥p(); 

 P≥p()P<p();P>p()P≤p(); 

 (12)12;(12)12. 

上述两类等价关系表明,我们只需在 PCTL的某个子集上讨论其限界模型检测问题.该子集与 PCTL具有相

同的表达力,且概率约束只能是≥p 或者>p,否定算子只能作用于原子命题.我们将该子集记为 PCTL≥. 

3.2   PCTL的限界语义 

定义 6(PCTL 的限界语义). 令 aAp 为原子命题,M=(S,P,sin,Ap,L)是离散时间马尔可夫链,sS,1,2 是 

PCTL≥状态公式,是 PCTL≥路径公式,k 为自然数(称为界).对于状态公式满足性关系k 定义为: 

 ska 当且仅当 aL(s); 

 sk12 当且仅当 sk1 且 sk2; 

 sk12 当且仅当 sk1 或者 sk2; 

 skP≥p()当且仅当 Pr(sk)≥p,这里,Pr(sk)=Prs({Paths(s)|k}). 

对于 M 中的路径,满足性关系k 定义为: 

 kX1 当且仅当 k≥1 且(1)k1; 

 kF1 当且仅当存在自然数 i≤k,使得(i)k1; 

 kG1 当且仅当对任意的自然数 i≤k,(i)k1,且存在自然数 0≤j≤k,使得 P((k),(j))>0,=(0)… 



 

 

 

1660 Journal of Software 软件学报 Vol.23, No.7, July 2012   

 

(j1)((j),…,(k)); 

 k1U2 当且仅当存在自然数 j≤k,使得(j)k2,且对任意小于 j 的自然数 i,(i)k1; 

 k1R2 当且仅当:1) 对任意的自然数 i≤k,(i)k2,且存在自然数 0≤j≤k,使得 P((k),(j))>0, 

=(0)…(j1)((j),…,(k));或者,2) 存在自然数 m≤k,使得(m)k1,且对任意小于 m 的自然数 

i,(i)k2. 

定理 1. 令 aAp 为原子命题,M=(S,P,sin,Ap,L)是离散时间马尔可夫链,sS,是 PCTL≥状态公式,k 为自然数. 

如果 sk,则 s. 

证明:采用对的长度进行归纳的方法来证明结论. 

Case 1. =a 

ska 说明 aL(s),由定义 4 中的满足性关系,直接可得 sa; 

Case 2. =12 

sk12 说明 sk1,sk2.由归纳假设可知:s1,s2,即 s12. 

Case 3. =12 

sk12 说明 sk1 或者 sk2.由归纳假设可知:s1 或者 s2,即 s12. 

Case 4. =P≥p() 

skP≥p()说明 Pr(sk)≥p,即 Pr(sk)=Prs({Paths(s)|k})≥p.对于时态算子 X,F,U,限界语义与文献

[15]中定义的一致,因此有k蕴含,从而 Prs({Paths(s)|})≥Prs({Paths(s)|k})≥p,即 sP≥p(). 

对于算子 R,1R2G22U(12),因此只需考察算子 G. 

令=G,设k,依据限界语义的定义,对任意自然数 i≤k,(i)k,由归纳可知:(i).又由限界语义的定

义可知,存在 0≤j≤k,使得 P((k),(j))>0,=(0)…(j1)((j),…,(k)),则i≥0,(i),即.因此, 

{Paths(s)|k}{Paths(s)|}, 

即 Pr(s)=Prs({Paths(s)|})≥Prs({Paths(s)|k})≥p. □ 

定理 1 表明,限界语义的定义是正确的.即,在局部空间中成立的属性在全局空间中也成立. 

3.3   限界模型检测过程终止的判断 

定理 1 告诉我们,如果存在自然数 k 使得 sk,则可推断出 s.现在的问题是,如果 s,则不存在自然数 k

使得 sk.换句话讲,当 sk时,我们面临两种选择:其一是增加 k 的值继续搜索,其二是停止搜索.因此,我们需要 

一个判别标准来判断当前状态下应该持有的选择.本节我们将探讨这种标准.首先回顾一下分支时态逻辑模型

检测中的完全界的概念. 

定义 7. 称自然数 CT 是完全界当且仅当如果 s,则一定存在自然数 k≤CT,使得 sk. 

在知道完全界 CT的情况下,当 sk时,如果 k不大于 CT,则增加 k的值继续搜索;否则停止搜索,并返回信息: 

s.对于分支时态逻辑或者线性时态逻辑的限界模型检测,完全界是存在的;但是对于 PCTL 限界模型检测,完 

全界则不一定存在. 

考察一个简单的通信协议[4],该协议的离散时间马尔可夫链如图 1 所示.start 是初始状态,且在 start 下产生 

一条消息.消息产生后,系统进入状态 try.在 try状态下,消息成功发送的概率为
9

10
,消息丢失的概率为

1

10
.并且在 

消息丢失的情况下,消息会被不断地发送,直至成功为止.发送成功后,系统返回初始状态. 

对于状态 s,引入原子命题 as 表示当前状态为 s.考察属性 P=1(Fadeliv),即消息发送成功的概率为 1.通过计算

发现: 

( | ) { ( ) | | }

                             { , ,( , ) , ,... | 0}

9 1 9 1 1 9 1 1 1 9
                             .

10 10 10 10 10 10 10 10 10 10

deliv start deliv

r
start

Pr start Fa Pr Paths start Fa

Pr start try lost try deliv r

 



   

 

          

≥

.. 1,

 



 

 

 

周从华 等:概率计算树逻辑的限界模型检测 1661 

 

即 startP=1(Fadeliv).令 k 为界,则 

( | ) { ( ) | | }

                               , ,( , ) , ,... | 1
2

9 1 9 1 1 9
                               ...

10 10 10 10 10 10

k deliv start k deliv

r
start

Pr start Fa Pr Paths start Fa

k
Pr start try lost try deliv r

 



   

    
 

       

≤

1 1 1
2 21 9 1

1 .
10 10 10

k k                   
   

 

deliv try lost
9

10 1

1
1

10

start

1

 

Fig.1  Discrete-Time Markov chain of a simple communication protocol 

图 1  一个简单通信协议的离散时间马尔可夫链 

比较 Pr(startFadeliv)和 Pr(startkFadeliv)可以发现,对于任意的有限界 k,Pr(startkFadeliv)<Pr(startFadeliv).

换句话讲,对于属性 P=1(Fadeliv),尽管 startP=1(Fadeliv),但不存在一个有限的自然数 k,使得 startkP=1(Fadeliv).因 

此,下面我们探讨在何种情况下完全界是存在的. 

对于 PCTL≥路径公式,满足的路径是一条无穷的状态演化序列.如果每一条路径均存在一个前缀满足,

则最长前缀序列的长度就是一个完全界. 

定理 2. 令 M=(S,P,sin,Ap,L)为离散时间马尔可夫链,是 PCTL≥路径公式.如果存在从初始状态 sin 出发的有 

限个状态序列 seq1,…,seqn,使得对任意满足的从 sin 出发的路径,均存在某个自然数 k 使得k,且(0),…,(k)

是 seq1,…,seqn中某个序列的子序列,则一定存在完全界 CT,使得 sinP≥r()时 sinkP≥r(),而且 CT不超过 seq1,…, 

seqn 中最长序列的长度. 

定理 2 的证明是直接的,这里不再给出.定理 2 告诉我们,如果对任意满足的路径均可找到一个有限状态序

列对其进行刻画,则完全界不会超过最长有限状态序列的长度. 

引理 1. 令 M=(S,P,sin,Ap,L)是离散时间马尔可夫链,是 PCTL 状态公式,是 PCTL 路径公式,则对于任意的 

自然数 k,我们有 sksk+1,kk+1. 

引理 1 的证明是平凡的,通过对 PCTL 公式的长度进行归纳即可得到,这里省略其证明过程.引理 1 告诉我 

们,Pr(s1),Pr(s2),…是一个递增的序列,且收敛于 Pr(s).由收敛的定义可知,对于小于 Pr(s)的实数 r,必

然存在整数 k,使得 Pr(sk)≥r,因此有下面的定理. 

定理 3. 令 M=(S,P,sin,Ap,L)为离散时间马尔可夫链,是 PCTL≥路径公式,p=Pr(sin),则对于公式 P≥r(sin) 

(r<p),一定存在完全界 CT,使得 sinP≥r()时 sinCTP≥r(). 

证明:由引理 1 可知,Pr(sink)随着 k 的增加而不断增加,且 lim ( | ) ( | )in k in
k

Pr s Pr s 


   .令=pr,由极限的

定义可知,存在自然数 k,当 k>k时,|Pr(sink)Pr(sin)|<. 

此时取 CT=k+1,则|Pr(sinCT)Pr(sin)|<,即 Pr(sinCT)>p,从而有 sinCTP≥r(). □ 

上述两个定理仅仅告诉我们在一些特殊的情形下完全界是存在的,但是对绝大多数情形而言不仅不知道

完全界是否存在,更不知道其有多大.因此,需要提出新的搜索过程终止的判别标准.我们引入数值计算方法中

牛顿迭代法常用的计算过程终止判别标准,即给定一个预先设置好的非常小的有理数,当相连两次概率度量



 

 

 

1662 Journal of Software 软件学报 Vol.23, No.7, July 2012   

 

计算结果的差控制在内时,计算终止. 

具体来讲,PCTL 限界模型检测过程如下. 

算法 1. PCTL 限界模型检测. 

输入:离散时间马尔可夫链 M=(S,P,sin,Ap,L),PCTL 路径公式,预先设置的终止标准; 

输出:Pr(sin). 

Step 1. 将转换为等价的 PCTL≥公式 
Step 2. 令 k=1,计算 Pr(sin0), Pr(sin1) 

Step 3. 

      While Pr(sink)Pr(sink1)≥ do 

      {令 k=k+1,计算 Pr(sink)} 

Step 4. 输出 Pr(sink) 

上述过程存在这样一个问题,即如何计算 Pr(sink),在第 3.4 节我们将探讨 Pr(sink)的计算问题. 

3.4   PCTL的限界模型检测算法 

本节我们将探讨如何将 sin 对 PCTL 公式的满足性关系判定问题转换为线性方程组的求解问题. 

对于 PCTL≥公式,我们假设其所有的子公式已经处理过,即对于的任意子公式,对于 S 中的每一个状态 

s,均已知 s 是否满足.令 k≥0 为限界模型检测的界,x(s,,k)=Pr(sk),S,k={sS|sk}.不同的时态算子对应着不 

同的转换方法,我们分别加以讨论.而对于原子命题及其否定、以及算子,因它们直观、简单,故此处忽略. 

Case 1. =X 

当 k=0 时,x(s,,0)=0;当 k≥1 时,
,

( , , ) ( , )
ks S

x s k P s s





  . 

Case 2. =F 

当 k=0 时:如果 s0,则 x(s,,0)=1;否则,x(s,,0)=0; 

当 k≥1 时:如果 sk,则 x(s,,k)=1;否则, ( , , ) ( , ) ( , , 1).
s S

x s k P s s x s k 


    

Case 3. =G 

对于任意的 sS,k,x(s,,k)=0;对于 sS,k,我们有: 

当 k=0 时,如果 P(s,s)=1,则 x(s,,0)=1;否则,x(s,,0)=0; 

当 k≥1 时,
0 , 0

0 1 1 1 1
0 ,...,

( , , ) lim ( , )... ( , )( ( , )... ( , ) ( , )) .
k k

k
n

i i i i k k k i
n

i s s S s s

x s k P s s P s s P s s P s s P s s


       

    

事实上,当 k≥1 时,我们计算的是 Prs{|s0=s,s1,…,skS,k,0≤i≤k,=s0,…,si1,(si,…,sk)
}. 

Case 4. =U 
当 k=0 时:如果 s0,则 x(s,,0)=1;否则,x(s,,0)=0; 

当 k≥1 时:如果 sk,则 x(s,,k)=0;否则, ( , , ) ( , ) ( , , 1).
s S

x s k P s s x s k 


    

Case 5. =R 
当 k=0 时:如果 s0,则 x(s,,0)=1;否则,x(s,,0)=0; 

当 k≥1 时,因为=RG(U()),故分成两部分: 

0 , ,

0 1 1 1 1
0 ,...,

( , , ) lim ( , )... ( , )( ( , )... ( , ) ( , )) ( , ( ), ).
k k k

k
n

i i i i k k k i
n

i s s S S

x s k P s s P s s P s s P s s P s s x s U k
 

   


     

     

这里,s0=s.对于同时满足 G,U()的路径,一定存在自然数 i,使得(i)k.因此在第 1 部分,令 s0,…,skS,k 

S,k,可以保证不重复计算 Prs({Paths(s)|kG�
The file is too long and its contents have been truncated.


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
可以，我按“**论文主线 + 模型检测三要素 + 关键公式怎么理解**”给你讲。这篇论文是：

**SAT-based bounded model checking for propositional projection temporal logic**，发表于 *Theoretical Computer Science* 2025，核心目标是把 **PPTL 的限界模型检测（BMC）** 转化成 **SAT 可满足性问题** 来求解。fileciteturn0file0

---

## 一、先说这篇论文到底在做什么

一句话概括：

**作者想把传统主要面向 LTL/CTL 的 SAT-based BMC，扩展到 PPTL（命题投影时序逻辑）上。**

为什么要做这个？

因为作者认为，LTL 和 CTL 虽然经典，但**表达能力不够“满正则”**，有些性质不容易表达，比如：

1. **时长/位置相关性质**\
   例如“性质 $P$ 在第 50 个状态成立”“在第 50 到第 100 个时间单位之间成立”。

2. **周期/重复性质**\
   例如带有类似 Kleene closure 的重复行为。

而 PPTL 是一种\*\*基于区间（interval-based）\*\*的时序逻辑，表达能力更强，作者强调它具有 **full regular expressiveness**，所以更适合描述这类系统性质。论文也明确说：本文先给出 PPTL 的限界语义，再把 BMC 规约为 SAT，最后用 MiniSAT 做实验，并用 RMS 调度算法作为案例。fileciteturn0file0

---

## 二、按“模型检测三要素”讲这篇论文

你之前常按“三要素”整理论文，这篇也非常适合。

### 1. 模型：Kripke 结构

论文中的系统模型是 **Kripke structure**：

$
M=(S,I,T,L)
$

其中：

- $S$：状态集合
- $I$：初始状态集合
- $T\subseteq S\times S$：迁移关系
- $L$：标记函数

这和经典模型检测一致。论文第 3.1 节先重新给了 Kripke 结构定义，再把路径看成区间来解释 PPTL。fileciteturn0file0

---

### 2. 逻辑：PPTL（命题投影时序逻辑）

PPTL 的基本语法在文中写成：

$
P ::= p \mid \circ P \mid \neg P \mid P_1 \vee P_2 \mid (P_1,\dots,P_m)\ prj\ P
$

核心算子只有两个原始时序算子：

- **next**：$\circ$
- **projection**：$prj$

其中 projection 是 PPTL 最关键、也最不同于 LTL/CTL 的地方。fileciteturn0file0

论文还定义了很多派生算子，比如：

- $\varepsilon \equiv \neg \circ \top$
- $P;Q \equiv (P,Q)\ prj\ \varepsilon$
- $\Diamond P \equiv \top;P$
- $\Box P \equiv \neg \Diamond \neg P$

也就是说，PPTL 里“顺序组合”“最终”“一直”等都能派生出来。fileciteturn0file0

---

### 3. 算法：SAT-based bounded model checking

论文真正的贡献在算法部分：

- 定义 **PPTL 的限界语义**
- 证明这种限界语义和原语义之间的对应关系
- 把“系统 $M$ 在界 $k$ 内满足 PPTL 公式 $f$”转成一个布尔公式
- 再交给 **SAT solver（MiniSAT）** 求解

也就是：

$
\text{BMC for PPTL} \quad \Longrightarrow \quad \text{SAT}
$

这就是这篇论文的核心。fileciteturn0file0

---

## 三、PPTL 为什么难？难点就在“区间”和“投影”

这篇论文比 LTL-BMC 难的地方，不在 SAT，而在 **PPTL 的语义本身**。

### 1. PPTL 是在“区间”上解释，不只是单一路径点

LTL 主要在“状态序列位置”上解释公式。  
PPTL 则是在**区间 interval** 上解释公式，区间可以是有限的，也可以是无限的。

论文定义：

- 一个状态序列 $\sigma=\langle s_0,s_1,\dots \rangle$ 称为区间
- 长度可以有限，也可以是 $\omega$

这意味着 PPTL 天然适合表达“某段过程发生了什么”。fileciteturn0file0

---

### 2. projection 算子是 PPTL 的灵魂

$
(P_1,\dots,P_m)\ prj\ Q
$

直观理解：

- 先把整个区间分成若干段
- 每一段分别满足 $P_1,\dots,P_m$
- 再把这些分段的“端点”投影出来，形成一个新的区间
- 然后让 $Q$ 在这个“投影区间”上成立

论文第 2 节还专门定义了 **projected interval**，并配图说明。你可以把它理解成：

> “我不关心整条原始路径的全部细节，我只抽取几个关键时刻，再在这些关键时刻构成的新区间上检查性质 $Q$。”

这就是 PPTL 能表达复杂时序结构的原因。fileciteturn0file0

---

## 四、论文的关键技术路线

---

### 第一步：把任意 PPTL 公式化成 Normal Form

论文给出 PPTL 的范式：

$
NF(Q)\equiv \bigvee(Q_{e_j}\land \varepsilon)\ \vee\ \bigvee(Q_i\land \circ Q_i')
$

简化写法就是：

$
NF(Q)\equiv Q_e\land \varepsilon \ \vee\ \bigvee_{i=1}^r(Q_i\land \circ Q_i')
$

其中：

- $Q_e$、$Q_i$ 都是状态公式
- $\varepsilon$ 表示“当前已经到区间末端”

这个范式非常关键，因为它把复杂 PPTL 公式统一整理成：

- 一类是“**在当前结束**”
- 一类是“**当前满足某个状态条件，并且下一步继续检查**”

这就为后面做**递归编码**创造了条件。fileciteturn0file0

---

### 第二步：定义限界语义

论文给定一个 bound $k$，定义 $(\sigma,i)\models_k P$，表示：

> 在区间 $\sigma$ 的第 $i$ 个位置开始，到第 $k$ 个位置为止，公式 $P$ 成立。

关键定义有：

- 原子命题：看当前状态真假
- $\neg P$：按否定解释
- $P_1\vee P_2$：按析取解释
- $\circ P$：跳到 successor 位置继续检查
- $\varepsilon$：当且仅当 $i=k$
- $\epsilon$：当且仅当 $i<k$

这里最关键的是 **successor 的定义**：

- 如果是普通有限路径，$succ(i)=i+1$
- 如果是一个带回路的 $k$-loop，那么在 $i=k$ 时，后继会跳回某个 $l$

这就是把**无限路径**压缩成“前缀 + 回环”的标准 BMC 思想，只不过这里应用到了 PPTL 上。fileciteturn0file0

---

### 第三步：证明限界语义和原语义的一致性

这是论文理论部分的核心。

#### 引理 1
如果 $\sigma$ 是一个 $k$-loop，那么：

$
\sigma \models_k f \iff \sigma \models f
$

意思是：

> 对于带环的无限路径，只要你把环压缩到长度 $k$ 的前缀里，限界语义和原本的无限语义是等价的。

#### 引理 2
如果 $\sigma$ 是有限区间，且 $\sigma\models f$，那么存在某个 $k$，使得：

$
\sigma \models_k f
$

意思是：

> 对有限路径，原语义成立，一定能在某个有限界上捕捉到。

#### 定理 2
进一步推广到整个系统 $M$：

$
M \models \exists f \iff \exists k\ge 0,\ M \models_k \exists f
$

意思就是：

> “存在一条满足 $f$ 的路径”  
> 等价于  
> “存在某个界 $k$，在 $k$ 限界内就能找到满足 $f$ 的路径”。

这就是 BMC 合法性的理论基础。fileciteturn0file0

---

## 五、最核心部分：怎样把 PPTL-BMC 编码成 SAT

这是你做汇报最该抓住的地方。

论文定义：

### 1. 系统展开部分 $M_k$

$
M_k \stackrel{def}{=} I(s_0)\land \bigwedge_{i=0}^{k-1}T(s_i,s_{i+1})
$

含义：

- $s_0$ 是初始状态
- $s_0\to s_1\to \cdots \to s_k$ 必须是系统的一条合法路径

这就是“路径展开”。

---

### 2. 回路条件 $L(k,l)$

$
L(k,l)\stackrel{def}{=}T(s_k,s_l), \quad 0\le l\le k
$

表示末状态 $s_k$ 能跳回 $s_l$，形成 loop。

再定义：

$
L_k \stackrel{def}{=} \bigvee_{l=0}^k L(k,l)
$

表示：存在某个 $l$，让长度 $k$ 的路径形成环。fileciteturn0file0

---

### 3. 公式翻译部分 $X_k$

论文分别讨论两类情况：

#### 情况 A：无 loop（有限路径）
把 $f$ 翻译成 $f(i,k)$

#### 情况 B：有 loop（无限路径被压缩）
把 $f$ 翻译成 $f(i,k,l)$

它们都按公式结构递归翻译：

- 原子命题：变成状态 $s_i$ 上的布尔变量
- 否定、析取：直接变成命题逻辑连接词
- next：跳到下一个位置
- $\varepsilon,\epsilon$：根据 $i$ 是否等于 $k$ 决定真假

---

### 4. 最终总编码

论文定义：

$
X_k \stackrel{def}{=} (\neg L_k \land f(0,k))\ \vee\ \bigvee_{l=0}^k (L(k,l)\land f(0,k,l))
$

再把系统和性质合起来：

$
[M,f]_k \stackrel{def}{=} M_k \land X_k
$

它的直观意义是：

- 先保证 $\langle s_0,\dots,s_k\rangle$ 是系统的一条合法路径；
- 然后分两种情况：
  - 没有环：用有限路径语义检查 $f$
  - 有环：用 loop 语义检查 $f$

最后得到一个**纯布尔公式**，交给 SAT 求解器。fileciteturn0file0

---

### 5. 关键正确性结论

论文给出：

$
[M,f]_k \text{ is satisfiable } \iff M \models_k \exists f
$

也就是说：

> SAT 可满足  
> 当且仅当  
> 系统里存在一条长度不超过 $k$ 的路径，在限界语义下满足 $f$。

这就把 PPTL 的限界模型检测，严密地变成了 SAT 求解问题。fileciteturn0file0

---

## 六、这篇论文和经典 BMC 的关系

这篇论文其实是在做一件很典型的工作：

### 经典 BMC
主要是：

- LTL / CTL
- 找反例
- 编码成 SAT

### 这篇论文
做的是：

- 把逻辑换成 **PPTL**
- 因为 PPTL 基于区间、还有 projection，语义更复杂
- 所以必须重新：
  - 定义 bounded semantics
  - 证明 bounded/unbounded 的对应
  - 给出新的 SAT 编码

换句话说，这不是“直接套 LTL-BMC”，而是**把 BMC 理论重新移植到 PPTL 上**。fileciteturn0file0turn0file1

---

## 七、案例：RMS（Rate Monotonic Scheduling）

论文第 4 节用 **RMS 调度算法** 做案例研究。  
作者想说明：PPTL 不只是理论上更强，而是能实际描述和验证调度系统中的时序性质。

RMS 是经典周期任务调度算法，任务优先级由周期决定。论文构造了相应的执行过程和 Kripke 结构，并用 SAT-based BMC 去验证相关调度性质。文中还给了执行图和 Kripke 结构图。fileciteturn0file0

你做汇报时可以这样概括这个案例的作用：

- **不是为了发明 RMS**
- 而是为了说明：
  1. PPTL 可以描述调度过程中的复杂时序行为；
  2. 他们提出的 SAT-based BMC 方法确实能跑起来；
  3. MiniSAT + 原型工具在实践上是可行的。

---

## 八、这篇论文的创新点

我帮你提炼成 4 个最适合答辩/汇报的点：

### 创新点 1：把 SAT-based BMC 扩展到了 PPTL
以前 SAT-based BMC 多围绕 LTL/CTL，这篇把它推广到了区间逻辑 PPTL。fileciteturn0file0

### 创新点 2：定义了 PPTL 的限界语义
这是基础，没有这个就没法做 BMC。fileciteturn0file0

### 创新点 3：证明了限界语义与原语义的对应关系
也就是论文中的若干引理和定理，保证方法不是拍脑袋，而是理论上正确。fileciteturn0file0

### 创新点 4：给出了从 PPTL-BMC 到 SAT 的具体规约
包括：

- 路径展开 $M_k$
- 回路条件 $L_k$
- 公式翻译 $f(i,k)$、$f(i,k,l)$
- 最终布尔公式 $[M,f]_k$

这就是算法落地的关键。fileciteturn0file0

---

## 九、这篇论文的局限

论文自己也承认，**BMC 天然不完备**。

也就是：

- 如果找到 counterexample / witness，就很有用；
- 如果在当前 $k$ 下找不到，并不能直接说明系统一定满足性质；
- 只能继续增大 $k$。

这也是所有 BMC 的共性，不是这篇独有的问题。论文在引言中就明确提到，BMC 的缺点是不能在有限搜索失败后直接证明“绝对无错误”。fileciteturn0file0turn0file1

另外，从研究角度看，这篇论文更偏：

- **理论定义 + 编码框架 + 原型验证**

而不是一个大规模工业级性能论文。所以如果你从“工程性能”角度提问，可以说：

> 它更重要的贡献是把 PPTL-BMC 的理论链条打通，而不是做出最强性能工具。

---

## 十、你做组会时可以直接这样总结

### 30 秒总结版
这篇论文研究 **PPTL 的 SAT 限界模型检测**。PPTL 比 LTL/CTL 表达能力更强，能描述区间性、时长性和重复性性质。论文先定义 PPTL 的限界语义，再证明限界语义与原语义之间的对应关系，最后把“系统在界 $k$ 内满足 PPTL 公式”的问题编码成 SAT 公式，由 MiniSAT 求解，并通过 RMS 调度案例验证方法的可行性。fileciteturn0file0

### 三要素版
- **模型**：Kripke 结构  
- **逻辑**：PPTL  
- **算法**：SAT-based bounded model checking

### 核心公式版
$
[M,f]_k = M_k \land \Big((\neg L_k\land f(0,k))\vee \bigvee_{l=0}^{k}(L(k,l)\land f(0,k,l))\Big)
$

解释：

- $M\_k$：展开系统路径
- $L\_k$：判断是否存在回路
  - $f(0,k)$ / $f(0,k,l)$：把 PPTL 性质翻译成布尔约束
- 最终交给 SAT solver 检查是否可满足。fileciteturn0file0

---

## 十一、如果你要更深入理解，这篇论文最该啃哪三部分

建议按这个顺序看：

1. **第 2 节 PPTL 基础**
   重点看 projection 和 normal form

2. **第 3.1 节 bounded semantics**
   重点看 $k$-loop、$succ(i)$、$\models_k$


3. **第 3.3 节 BMC 到 SAT 的规约**
   重点看 $M_k$、$L_k$、$[M,f]_k$


---

接下来你要是愿意，我可以继续给你做两种内容中的一种：\
**一种是“按论文原文公式逐行细讲第3节”**，另一种是\*\*“直接整理成组会PPT提纲”\*\*。


#### You:
讲解一下第一节

#### ChatGPT:
\[Unsupported Content]


#### Plugin (file_search):
Make sure to include fileciteturn2file0 in your response to cite this file, or to surface it as a link.
<PARSED TEXT FOR PAGE: 1 / 17>
Theoretical Computer Science 1049 (2025) 115368
Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
Contents lists available at ScienceDirect
Theoretical Computer Science
journal homepage: www.elsevier.com/locate/tcs
SAT-based bounded model checking for propositional projection
temporal logic ✩
Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a
a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China b China Academy of Space Technology, Beijing 100094, China
A R T I C L E I N F O A B S T R A C T
Section Editor: Paul G. Spirakis
Handling Editor: Ding-Zhu Du
Keywords:
Propositional projection temporal logic
Bounded model checking
Rate monotonic scheduling
This paper presents a bounded model checking (BMC) approach for propositional projection
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed
in the paper is useful and feasible.
1. Introduction
Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted,
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware,
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀⊧𝜙?). With temporal logics, linear-time temporal
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8]
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9].
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC)
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs.
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC
✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.
* Corresponding authors.
E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn
(C. Yu), yangmf@bice.org.cn (M. Yang).
https://doi.org/10.1016/j.tcs.2025.115368
Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025
<PARSED TEXT FOR PAGE: 2 / 17>
Theoretical Computer Science 1049 (2025) 115368
2
Z. Duan, C. Tian, N. Zhang et al.
is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥.
As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors
such as EBMC [20] are used in the verification of large-scale hardware and software systems.
Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.
With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach,
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.
The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the
conclusion is drawn in section 8.
2. Propositional projection temporal logic
To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL)
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to
[26].
2.1. Syntax:
PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:
𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑃
where 𝑝 ∈ 𝑃 𝑟𝑜𝑝 and 𝑃,𝑃1,…, 𝑃𝑖,…, 𝑃𝑙,…, 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙, 𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal
operators, otherwise it is called a temporal formula.
2.2. Semantics:
Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 = 𝑁 ∪ {𝜔} and extend
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁, 𝑖 < 𝜔, 𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as
≤ −{(𝜔,𝜔)}.
A state 𝑠𝑖 is a mapping from 𝑃 𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠|𝜎|⟩.
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote
the subinterval ⟨𝑠𝑖,…, 𝑠𝑗 ⟩ and 𝜎(𝑘)
(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,…, 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔
while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗<𝑖, in this case, 𝜎(𝑖..𝑗) = . Note that, 
denotes void (for nothing) and its length || is -1.
Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.
<PARSED TEXT FOR PAGE: 3 / 17>
Theoretical Computer Science 1049 (2025) 115368
3
Z. Duan, C. Tian, N. Zhang et al.
Fig. 1. Projected Intervals.
Fig. 2. Three cases of (𝑃1,…, 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)
𝜎1 ⋅ 𝜎2 =
⎧
⎪
⎪
⎨
⎪
⎪
⎩
𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ,
𝜎2, if 𝜎1 = ,
⟨𝑠0,…, 𝑠𝑖, 𝑠𝑖+1,…, 𝑠𝑗 ⟩, if 𝜎1 = ⟨𝑠0,…, 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,…, 𝑠𝑗 ⟩,
𝑗 ≤ 𝜔,|𝜎1| ≠ 𝜔.
It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1| + |𝜎2| and for any interval 𝜎,  ⋅ 𝜎 = 𝜎 ⋅  = 𝜎.
For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the
same successive state to produce different projected states, we define the projected interval:
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚) = ⟨𝑠𝑡0
, 𝑠𝑡1
,…, 𝑠𝑡𝑛
⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ …𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁, and 𝑡0, 𝑡1,…, 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,…, 𝑟𝑚 by deleting
all duplicates. That is, 𝑡0,…, 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,…, 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case,
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1, 𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected
intervals are given below (See Fig. 1).
(a) ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 3, 4, 4, 4, 6) = ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 4, 6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0, 0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47, 47, 𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47) = ⟨𝑠0, 𝑠21, 𝑠47⟩
Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1,…, 𝑃𝑚 are interpreted
in the projection construct. In order to interpret the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞
as follows:
Let 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠𝑚,…, 𝑠𝑗 ⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is
interpreted over a subinterval 𝜎(𝑟𝑖−1..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,…, 𝑠𝑟𝑖
⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination
of 𝑃𝑚 (see red color sequence).
Thus, we define 𝜎𝑞 as follows:
𝜎(𝑟𝑚+1..𝑗) =
{ < 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,
, if 𝑟𝑚 = 𝑗.
𝜎𝑞 = 𝜎 ↓ (𝑟0,…, 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)
<IMAGE FOR PAGE: 3 / 17>
![image](sediment://7a41b68aec6f5e2#file_00000000677c7209a156353e1c071784#p_2.jpg)
<PARSED TEXT FOR PAGE: 4 / 17>
Theoretical Computer Science 1049 (2025) 115368
4
Z. Duan, C. Tian, N. Zhang et al.
Table 1
Derived formulas.
A1 𝜀
def
= ¬ ○ ⊤ A2 𝜖def
= ○⊤
A3 ⨀𝑃 def
= 𝜀 ∨ ○𝑃 A4 𝑃 ;𝑄 def
= (𝑃,𝑄) 𝑝𝑟𝑗 𝜀
A5 ◊ 𝑃 def
= ⊤;𝑃 A6 □𝑃 def
= ¬◊¬𝑃
A7 𝑓 𝑖𝑛 def
= ◊𝜀 A8 𝑖𝑛𝑓 def
= ¬𝑓 𝑖𝑛
A9 {
○0𝑃 def
= 𝑃
○𝑛𝑃 def
= ○(○𝑛−1𝑃 )(𝑛 > 0)
A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧ 𝑄 ∨ 𝑃 ∧ (𝑄;⊤)
∨𝑃 ∧ 𝑄 ∧ □ 𝜖
A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)
𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.
PPTL formulas are interpreted over intervals. An interpretation  = (𝜎, 𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,…, 𝑠𝑗 ⟩ of 𝜎 with the current state
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎⊧𝑃
if 𝜎(0,|𝜎|) ⊧ 𝑃 .
(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.
(2)  ⊧ ○𝑃 iff 𝑘<𝑗 and (𝜎,𝑘 + 1, 𝑗) ⊧ 𝑃 .
(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .
(4)  ⊧ 𝑃 ∨ 𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.
(5)  ⊧ (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎,𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all
1 ≤ 𝑙 ≤ 𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞 , 0,|𝜎𝑞 |) ⊧ 𝑄).
Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎⊧𝑝, if (𝜎, 0,|𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable
if 𝜎⊧𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎⊧𝑝 for all 𝜎.
Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤ def
= 𝑃 ∨ ¬𝑃 and ⊥ def
= 𝑃 ∧ ¬𝑃 , for any
formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.
2.3. Normal form
Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL
formula 𝑄. Then, the NF can be defined as follows:
Definition 1. Normal Form of 𝑄:
𝑁𝐹(𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀)∨∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧ ○𝑄′
𝑖
)
To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟
𝑖=1(𝑄𝑖 ∧ ○𝑄′
𝑖
) to replace
∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧ ○𝑄′
𝑖
). Thus,
𝑁𝐹(𝑄) ≡ 𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧ ○𝑄′
𝑖
)
where 𝑄𝑒 and 𝑄𝑖 are state formulas.
Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.
The proof of this theorem can be found in [26].
Example 1. Given a PPTL formula 𝑓, 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get
𝑁𝐹(𝑓) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀)∨(𝑟 ∧ 𝑝 ∧ ○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ ○⊤)∨(𝑟 ∧ 𝑝 ∧ ○(⊤; (𝑞;⊤)))
3. Principle of SAT-based bounded model checking with PPTL
In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖
. In the following, we define the bounded semantics of PPTL formulas.
Let 𝜎 be an interval and 𝑃 a PPTL formula.
<PARSED TEXT FOR PAGE: 5 / 17>
Theoretical Computer Science 1049 (2025) 115368
5
Z. Duan, C. Tian, N. Zhang et al.
Fig. 3. 𝜎 is a 𝑘 − 𝑙𝑜𝑜𝑝.
3.1. Bounded semantics
In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.
Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼,𝑇,𝐿) where 𝑆 is the set of sates, 𝐼⊆𝑆 is the set of initial states,
𝑇 ⊆𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.
We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite.
Therefore, in the following, we give the definition of 𝑘 − 𝑙𝑜𝑜𝑝 in an interval.
Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,…, 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,…, 𝑠𝑘⟩𝜔, we call
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.
Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈ 𝑁0. Now we can define the successor of state
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:
𝑠𝑢𝑐𝑐(𝑖) =
⎧
⎪
⎨
⎪
⎩
𝑖 + 1 if 𝑖<𝑘
𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝
𝑘 + 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval
With bounded model checking of PPTL, given a bound 𝑘 ∈ 𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval
< 𝑠𝑖,…, 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .
The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:
(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃 𝑟𝑜𝑝 is an atomic proposition
(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃
(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃
(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘
(𝜎, 𝑖) ⊧𝑘
𝜖 iff 𝑖<𝑘
A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎, 0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have
𝜎 ⊧𝑘 𝑃 iff (𝜎, 0, 𝑘) ⊧ 𝑃 .
As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics
of PPTL is sound.
3.2. Bounded model checking
According to the structure of interval 𝜎, two basic lemmas are given below:
Lemma 1. Let 𝑘 ∈ 𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘 − 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎⊧𝑓.
Proof. To prove Lemma 1, we first prove a stronger conclusion given below:
(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)
Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓:
Base case:
𝑓 ≡ 𝑝 ∈ 𝑃 𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖,|𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖,|𝜎|) ⊧ 𝑝.
<PARSED TEXT FOR PAGE: 6 / 
The file is too long and its contents have been truncated.


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
可以。**第一节就是引言（Introduction）**，这一节的作用不是讲具体算法细节，而是回答 4 个问题：

1. **研究背景是什么**
2. **现有方法有什么不足**
3. **为什么要引入 PPTL**
4. **这篇论文到底做了什么贡献**

我按这个顺序给你讲。

---

## 一、第一节在讲什么

作者一开头先回顾了\*\*模型检测（Model Checking）\*\*的基本背景：\
模型检测是由 Clarke 和 Emerson、以及 Queille 和 Sifakis 独立提出的，是一种自动化验证技术，广泛用于硬件、软件和通信协议验证。它要回答的问题是：

$
M \models \varphi\ ?
$

也就是：**系统 $M$ 是否满足时序逻辑公式 $\varphi$**。论文里还提到，实际中最常用的描述逻辑是 **LTL** 和 **CTL**。fileciteturn2file0

这一段其实是在铺垫：  
**“我们讨论的问题仍然属于经典模型检测框架。”**

也就是说，这篇论文并不是脱离模型检测另起炉灶，而是在经典模型检测体系里，研究一种新的逻辑和新的限界检查方法。

---

## 二、作者先指出模型检测的老问题：状态爆炸

接着作者说，随着系统组件数量增加，系统状态数会指数增长，这就导致了著名的**状态爆炸问题（state explosion problem）**。fileciteturn2file0

这里你可以这样理解：

- 一个小系统可能只有几十个状态；
- 但多个模块一组合，状态数可能瞬间变成几万、几百万；
- 模型检测理论上能做，但实践中会变得非常难算。

所以第一节先回顾了几类经典缓解方法：

### 1. BDD 符号模型检测
作者提到基于 **BDD** 的符号模型检测，代表工具如 **NuSMV**。  
思路是：不显式枚举所有状态，而是用符号方式压缩表示。fileciteturn2file0

### 2. 组合模型检测
把大系统拆成多个部分分别验证，从而降低复杂度。fileciteturn2file0

### 3. BMC（Bounded Model Checking）
作者特别强调 **BMC 是符号模型检测之后的重要进展**，而且已经很成功，也出现了很多工具，比如 **CBMC、CPAChecker、ESBMC**。fileciteturn2file0

所以这一段的逻辑是：

> 模型检测很好，但有状态爆炸；  
> 为了解决它，人们提出了很多办法；  
> 其中 **BMC 是非常重要的一条路线**。

这就自然引出了论文主题。

---

## 三、作者解释什么是 BMC，以及它的优缺点

论文第一节对 BMC 的解释其实很重要。

作者说，**BMC 的核心思想**是：

> 给定一个整数界 $k$，只检查长度不超过 $k$ 的路径。  
> 如果在这个范围内发现性质不满足，就找到错误；  
> 如果没发现，也**不能直接说明系统一定正确**，只能考虑继续增大 $k$。 fileciteturn2file0

这句话你一定要理解透，因为这是整篇论文的出发点。

### BMC 的优点
- 它把搜索限制在有限长度内；
- 因此比直接做全状态空间搜索更可控；
- 特别适合**找反例、找 bug**。

### BMC 的缺点
- **不完备（incomplete）**
- 你在当前 $k$ 下没找到错误，不代表系统真的没错；
- 只能说明：**在这个界之内没发现问题**。fileciteturn2file0

这个“不完备性”是 BMC 的天生属性，不是这篇论文特有的问题。

---

## 四、为什么要把 BMC 和 SAT 结合

接下来作者引入 **SAT-based BMC**。

论文说，SAT-based BMC 的做法是：

- 把有限长度的系统路径；
- 再加上时序逻辑公式；
- 一起编码成一个**布尔公式**；
- 然后把“找反例”变成“判断这个布尔公式是否可满足”。fileciteturn2file0

也就是：

$
\text{BMC问题} \quad \longrightarrow \quad \text{SAT问题}
$

作者还强调，虽然 SAT 理论上是 NP-complete，但现代 SAT 求解器，尤其像 **MiniSAT**，在实际问题上表现很好，能够处理大量变量和子句，所以 SAT-based BMC 在复杂系统验证中很有潜力。fileciteturn2file0

这一段的真实意思是：

> “我们不是单纯做一个逻辑理论，而是想借助现代 SAT 求解器，把验证做得更高效、更可落地。”

---

## 五、第一节最关键的转折：LTL/CTL 表达能力不够

这是第一节里**最核心的动机**。

作者说：当前很多 SAT-based BMC 都是用 **LTL 或 CTL** 来写系统性质。\
但 **LTL 和 CTL 的表达能力不是 full regular 的**，因此有些实际性质它们不擅长表达。fileciteturn2file0

作者举了两类典型例子：

### 1. 与“时长/位置”有关的性质

比如：

- 性质 $P$ 在第 50 个状态成立；
  - $P$ 在第 50 到第 100 个时间单位之间成立。

### 2. 周期性、重复性性质

比如类似 **Kleene closure** 的反复重复行为。fileciteturn2file0

作者的结论是：

> 只用 LTL/CTL 来描述系统性质，在某些场景下是不够的。

这句话很重要，因为它回答了：

**“为什么这篇论文不继续做 LTL/CTL，而要换逻辑？”**

---

## 六、为什么选 PPTL

作者接着说，为了更充分地描述系统性质，他们选择 **PPTL（Propositional Projection Temporal Logic）** 作为性质描述逻辑。原因是：

- PPTL 是一种**区间时序逻辑**
- 它有 **full regular expressiveness**
- 更适合表达**完整正则性质**和**时间长度相关性质**。fileciteturn2file0

这里你可以这样理解：

### LTL/CTL 更像是在问：

- 当前是否成立？
- 下一步是否成立？
- 将来某时是否成立？
- 所有路径/存在路径上是否成立？

### PPTL 更擅长问：

- 在**这一段区间**里发生了什么？
- 一个性质是否先发生，再发生另一个？
- 某个行为模式是否重复出现？
- 从若干关键点“投影”出来的新区间上，性质是否成立？

所以 PPTL 比 LTL/CTL 更适合描述复杂的**过程型、区间型、正则型**行为。

---

## 七、作者指出：PPTL 已经有基础，但还缺 SAT-BMC

第一节不是说 PPTL 完全没人做过。作者回顾说：

- PTL/PPTL 社区已经形式化并证明了很多逻辑定律；
- 已经有 PPTL 公式可满足性判定过程；
- 甚至已经有基于 **SPIN** 的 PPTL 模型检测器。fileciteturn2file0

这说明：

> PPTL 本身不是新逻辑，已经有理论基础，也有一定工具支持。

但是，作者马上指出：

- 即便是基于 SPIN 的 PPTL 模型检测器；
- 也仍然会受到**状态爆炸问题**影响。fileciteturn2file0

于是论文的研究动机就非常清楚了：

> 既然 PPTL 表达能力强，\
> 但现有 PPTL 检测又受状态爆炸限制，\
> 那就自然想到：\
> **能不能给 PPTL 也做一个 SAT-based bounded model checking？**

这就是整篇论文真正的问题意识。

---

## 八、第一节总结了本文贡献

作者在引言最后明确说了本文做的几件事：

### 1. 定义 PPTL 的限界语义

也就是先说明：在给定边界 $k$ 时，PPTL 公式该怎么解释。fileciteturn2file0

### 2. 建立限界模型检测和基本模型检测之间的关系

作者会证明一些引理和定理，说明 bounded semantics 和原有 semantics 之间怎么对应。fileciteturn2file0

### 3. 把 PPTL 的 BMC 归约为 SAT

这是算法核心：把问题交给 SAT solver 解。fileciteturn2file0

### 4. 用 RMS 算法作为案例

作者通过验证 **Rate Monotonic Scheduling (RMS)** 的可行性来说明方法能实际运行。fileciteturn2file0

### 5. 做了一个原型工具

论文提到结合 **Tseitin 编码** 和 **MiniSAT**，并基于 **NuSMV2** 搭建了原型系统。fileciteturn2file0

所以你汇报时可以把第一节的“本文贡献”概括成一句话：

> 本文提出了一种**面向 PPTL 的 SAT-based bounded model checking 方法**，从语义、理论到实现都做了完整打通。

---

## 九、第一节的逻辑链，你可以这样记

整节引言其实是一个非常标准的论文动机链：

### 第一步：模型检测很重要

广泛应用于硬件、软件、通信协议。fileciteturn2file0

### 第二步：但有状态爆炸

因此需要优化方法。fileciteturn2file0

### 第三步：BMC 是很有效的方法

但通常依赖 LTL/CTL。fileciteturn2file0

### 第四步：LTL/CTL 表达能力不足

有些时间长度、周期重复性质不好表达。fileciteturn2file0

### 第五步：PPTL 表达能力更强

适合描述 full regular properties。fileciteturn2file0

### 第六步：但 PPTL 现有模型检测仍有状态爆炸

所以需要 SAT-based BMC。fileciteturn2file0

### 第七步：本文提出 PPTL 的 SAT-based BMC

并给出语义、理论、规约和案例。fileciteturn2file0

---

## 十、如果你做组会，第一节可以讲成这一页

你可以直接讲成下面这种结构：

**第一节引言的核心内容：**

- 模型检测用于验证系统是否满足时序逻辑性质；
- 传统模型检测存在状态爆炸问题；
- BMC 通过限制搜索深度 $k$ 缓解状态爆炸，但本质上是不完备的；
- 现有 SAT-based BMC 主要基于 LTL/CTL；
- LTL/CTL 不能充分表达时长性质和周期重复性质；
- 因此作者引入具有 full regular expressiveness 的 PPTL；
- 论文目标是提出 **SAT-based BMC for PPTL**，并通过 RMS 案例验证可行性。fileciteturn2file0

---

## 十一、你容易在第一节里忽略的两个点

### 1. 这篇论文不是在“发明 BMC”

BMC 本身早就有了。\
这篇论文是在做：

> **把 BMC 从 LTL/CTL 逻辑，推广到 PPTL 逻辑。**

### 2. 这篇论文不是只讲逻辑表达能力

作者不是单纯说“PPTL 更强”。\
真正目标是：

> **既要保留 PPTL 的强表达能力，又要借助 SAT 求解器提高验证可行性。**

也就是“表达能力”和“求解效率”两头都要抓。

---

## 十二、一句话总结第一节

**第一节的本质就是：先说明传统 SAT-based BMC 大多依赖 LTL/CTL，而它们对某些区间型、时长型、重复型性质表达不足；因此作者选择表达能力更强的 PPTL，并提出一种将 PPTL 的限界模型检测归约为 SAT 的方法。** fileciteturn2file0

你要的话，我下一步可以继续给你**逐段讲第二节 2.1 语法和 2.2 语义**，尤其是把最难的 **projection（prj）算子**讲明白。


#### You:
什么是kleene闭包

#### ChatGPT:
**Kleene 闭包**（也叫 **Kleene star，克林闭包/克林星**）是形式语言里的一个基本运算，记作：

$
L^*
$

其中 $L$ 是一个语言，$L^*$ 表示：

> **把 $L$ 中的字符串重复 0 次、1 次、2 次、3 次……所能得到的所有字符串的集合。**

---

## 1. 数学定义

如果 $L$ 是一个语言，那么：

$
L^*=\bigcup_{n\ge 0} L^n
$

其中：

- $L^0=\{\varepsilon\}$，这里 $\varepsilon$ 表示**空串**
- $L^1=L$
- $L^2=\{xy \mid x\in L,\ y\in L\}$
- $L^3=\{xyz \mid x,y,z\in L\}$
- …

所以 $L^*$ 的意思就是：

$
L^*=\{\varepsilon\}\cup L\cup L^2\cup L^3\cup\cdots
$

---

## 2. 最直观的理解

你可以把它理解成：

> **“某种模式可以重复任意多次，包括一次也不重复。”**

---

## 3. 例子

### 例1：单个字符

设

$
L=\{a\}
$

那么：

- $L^0=\{\varepsilon\}$
- $L^1=\{a\}$
- $L^2=\{aa\}$
- $L^3=\{aaa\}$

所以：

$
L^*=\{\varepsilon,a,aa,aaa,\dots\}
$

也就是**任意多个 $a$**。

---

### 例2：两个字符串

设

$
L=\{ab,c\}
$

那么 $L^*$ 中包含：

- $\varepsilon$
- $ab$
- $c$
- $abab$
- $abc$
- $cab$
- $cc$
- $abccab$

等等。

因为你每次都可以从 $\{ab,c\}$ 里拿一个串出来，再拼接很多次。

---

## 4. 和 “+” 的区别

有时你还会看到 **Kleene plus**，记作：

$
L^+
$

它表示：

> 至少重复 1 次

所以：

$
L^+=L\cup L^2\cup L^3\cup\cdots
$

而：

$
L^*=L^+\cup\{\varepsilon\}
$

区别就在于：

- $L^*$：允许 **0 次**
- $L^+$：至少 **1 次**

---

## 5. 在正则表达式里怎么理解

在正则表达式中，星号 `*` 就是 Kleene 闭包。

例如：

- `a*`：表示 0 个或多个 `a`
- `(ab)*`：表示 0 次或多次重复 `ab`
- `(0|1)*`：表示由 0 和 1 构成的任意长度字符串

比如 `(ab)*` 对应的字符串有：

$
\varepsilon,\ ab,\ abab,\ ababab,\dots
$

---

## 6. 为什么你那篇论文会提到它

你刚才那篇论文在第一节说：

> LTL/CTL 对某些带有 **Kleene closure** 的性质表达能力不足。

它的意思不是说 LTL 完全不能写“重复”，而是说：

- **PPTL** 更擅长表达“一个行为模式重复多次”的**区间结构**
- 而这种“重复若干次”的思想，和形式语言中的 **Kleene 闭包** 很像

比如一个过程：

- 先执行 $P$
- 再执行 $Q$
- 然后这个整体过程重复很多次

这种“模式反复出现”的描述，就带有 Kleene star 的味道。

---

## 7. 再给你一个和时序逻辑贴近的直观理解

假设一个系统行为模式是：

$
\text{请求} \rightarrow \text{处理} \rightarrow \text{响应}
$

如果这个模式会不断重复出现，那么从形式语言角度可以看成类似：

$
(\text{请求·处理·响应})^*
$

意思是：

- 可以不发生
- 可以发生一次
- 可以发生两次
- 可以无限多次有限重复

这就是 Kleene 闭包的直观含义。

---

## 8. 一句话总结

**Kleene 闭包 $L^*$ 就是：把语言 $L$ 中的串进行任意次拼接（包括 0 次）后得到的所有字符串集合。它表示一种“可重复任意多次”的模式。**

---

你要的话，我下一步可以继续给你讲 **“为什么说 PPTL 比 LTL 更容易表达带 Kleene 闭包味道的性质”**。


#### You:
逐句讲解第二节

#### ChatGPT:
\[Unsupported Content]


#### Plugin (file_search):
Make sure to include fileciteturn4file0 in your response to cite this file, or to surface it as a link.
<PARSED TEXT FOR PAGE: 1 / 17>
Theoretical Computer Science 1049 (2025) 115368
Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
Contents lists available at ScienceDirect
Theoretical Computer Science
journal homepage: www.elsevier.com/locate/tcs
SAT-based bounded model checking for propositional projection
temporal logic ✩
Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a
a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China b China Academy of Space Technology, Beijing 100094, China
A R T I C L E I N F O A B S T R A C T
Section Editor: Paul G. Spirakis
Handling Editor: Ding-Zhu Du
Keywords:
Propositional projection temporal logic
Bounded model checking
Rate monotonic scheduling
This paper presents a bounded model checking (BMC) approach for propositional projection
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed
in the paper is useful and feasible.
1. Introduction
Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted,
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware,
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀⊧𝜙?). With temporal logics, linear-time temporal
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8]
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9].
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC)
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs.
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC
✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.
* Corresponding authors.
E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn
(C. Yu), yangmf@bice.org.cn (M. Yang).
https://doi.org/10.1016/j.tcs.2025.115368
Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025
<PARSED TEXT FOR PAGE: 2 / 17>
Theoretical Computer Science 1049 (2025) 115368
2
Z. Duan, C. Tian, N. Zhang et al.
is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥.
As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors
such as EBMC [20] are used in the verification of large-scale hardware and software systems.
Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.
With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach,
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.
The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the
conclusion is drawn in section 8.
2. Propositional projection temporal logic
To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL)
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to
[26].
2.1. Syntax:
PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:
𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑃
where 𝑝 ∈ 𝑃 𝑟𝑜𝑝 and 𝑃,𝑃1,…, 𝑃𝑖,…, 𝑃𝑙,…, 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙, 𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal
operators, otherwise it is called a temporal formula.
2.2. Semantics:
Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 = 𝑁 ∪ {𝜔} and extend
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁, 𝑖 < 𝜔, 𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as
≤ −{(𝜔,𝜔)}.
A state 𝑠𝑖 is a mapping from 𝑃 𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠|𝜎|⟩.
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote
the subinterval ⟨𝑠𝑖,…, 𝑠𝑗 ⟩ and 𝜎(𝑘)
(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,…, 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔
while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗<𝑖, in this case, 𝜎(𝑖..𝑗) = . Note that, 
denotes void (for nothing) and its length || is -1.
Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.
<PARSED TEXT FOR PAGE: 3 / 17>
Theoretical Computer Science 1049 (2025) 115368
3
Z. Duan, C. Tian, N. Zhang et al.
Fig. 1. Projected Intervals.
Fig. 2. Three cases of (𝑃1,…, 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)
𝜎1 ⋅ 𝜎2 =
⎧
⎪
⎪
⎨
⎪
⎪
⎩
𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ,
𝜎2, if 𝜎1 = ,
⟨𝑠0,…, 𝑠𝑖, 𝑠𝑖+1,…, 𝑠𝑗 ⟩, if 𝜎1 = ⟨𝑠0,…, 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,…, 𝑠𝑗 ⟩,
𝑗 ≤ 𝜔,|𝜎1| ≠ 𝜔.
It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1| + |𝜎2| and for any interval 𝜎,  ⋅ 𝜎 = 𝜎 ⋅  = 𝜎.
For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the
same successive state to produce different projected states, we define the projected interval:
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚) = ⟨𝑠𝑡0
, 𝑠𝑡1
,…, 𝑠𝑡𝑛
⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ …𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁, and 𝑡0, 𝑡1,…, 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,…, 𝑟𝑚 by deleting
all duplicates. That is, 𝑡0,…, 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,…, 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case,
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1, 𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected
intervals are given below (See Fig. 1).
(a) ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 3, 4, 4, 4, 6) = ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 4, 6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0, 0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47, 47, 𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47) = ⟨𝑠0, 𝑠21, 𝑠47⟩
Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1,…, 𝑃𝑚 are interpreted
in the projection construct. In order to interpret the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞
as follows:
Let 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠𝑚,…, 𝑠𝑗 ⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is
interpreted over a subinterval 𝜎(𝑟𝑖−1..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,…, 𝑠𝑟𝑖
⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination
of 𝑃𝑚 (see red color sequence).
Thus, we define 𝜎𝑞 as follows:
𝜎(𝑟𝑚+1..𝑗) =
{ < 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,
, if 𝑟𝑚 = 𝑗.
𝜎𝑞 = 𝜎 ↓ (𝑟0,…, 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)
<IMAGE FOR PAGE: 3 / 17>
![image](sediment://7a41b68aec6f5e2#file_00000000677c7209a156353e1c071784#p_2.jpg)
<PARSED TEXT FOR PAGE: 4 / 17>
Theoretical Computer Science 1049 (2025) 115368
4
Z. Duan, C. Tian, N. Zhang et al.
Table 1
Derived formulas.
A1 𝜀
def
= ¬ ○ ⊤ A2 𝜖def
= ○⊤
A3 ⨀𝑃 def
= 𝜀 ∨ ○𝑃 A4 𝑃 ;𝑄 def
= (𝑃,𝑄) 𝑝𝑟𝑗 𝜀
A5 ◊ 𝑃 def
= ⊤;𝑃 A6 □𝑃 def
= ¬◊¬𝑃
A7 𝑓 𝑖𝑛 def
= ◊𝜀 A8 𝑖𝑛𝑓 def
= ¬𝑓 𝑖𝑛
A9 {
○0𝑃 def
= 𝑃
○𝑛𝑃 def
= ○(○𝑛−1𝑃 )(𝑛 > 0)
A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧ 𝑄 ∨ 𝑃 ∧ (𝑄;⊤)
∨𝑃 ∧ 𝑄 ∧ □ 𝜖
A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)
𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.
PPTL formulas are interpreted over intervals. An interpretation  = (𝜎, 𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,…, 𝑠𝑗 ⟩ of 𝜎 with the current state
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎⊧𝑃
if 𝜎(0,|𝜎|) ⊧ 𝑃 .
(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.
(2)  ⊧ ○𝑃 iff 𝑘<𝑗 and (𝜎,𝑘 + 1, 𝑗) ⊧ 𝑃 .
(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .
(4)  ⊧ 𝑃 ∨ 𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.
(5)  ⊧ (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟�
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn4file1 in your response to cite this file, or to surface it as a link.
<PARSED TEXT FOR PAGE: 1 / 17>
Theoretical Computer Science 1049 (2025) 115368
Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
Contents lists available at ScienceDirect
Theoretical Computer Science
journal homepage: www.elsevier.com/locate/tcs
SAT-based bounded model checking for propositional projection
temporal logic ✩
Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a
a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China b China Academy of Space Technology, Beijing 100094, China
A R T I C L E I N F O A B S T R A C T
Section Editor: Paul G. Spirakis
Handling Editor: Ding-Zhu Du
Keywords:
Propositional projection temporal logic
Bounded model checking
Rate monotonic scheduling
This paper presents a bounded model checking (BMC) approach for propositional projection
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed
in the paper is useful and feasible.
1. Introduction
Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted,
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware,
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀⊧𝜙?). With temporal logics, linear-time temporal
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8]
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9].
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC)
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs.
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC
✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.
* Corresponding authors.
E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn
(C. Yu), yangmf@bice.org.cn (M. Yang).
https://doi.org/10.1016/j.tcs.2025.115368
Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025
<PARSED TEXT FOR PAGE: 2 / 17>
Theoretical Computer Science 1049 (2025) 115368
2
Z. Duan, C. Tian, N. Zhang et al.
is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥.
As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors
such as EBMC [20] are used in the verification of large-scale hardware and software systems.
Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.
With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach,
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.
The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the
conclusion is drawn in section 8.
2. Propositional projection temporal logic
To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL)
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to
[26].
2.1. Syntax:
PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:
𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑃
where 𝑝 ∈ 𝑃 𝑟𝑜𝑝 and 𝑃,𝑃1,…, 𝑃𝑖,…, 𝑃𝑙,…, 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙, 𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal
operators, otherwise it is called a temporal formula.
2.2. Semantics:
Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 = 𝑁 ∪ {𝜔} and extend
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁, 𝑖 < 𝜔, 𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as
≤ −{(𝜔,𝜔)}.
A state 𝑠𝑖 is a mapping from 𝑃 𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠|𝜎|⟩.
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote
the subinterval ⟨𝑠𝑖,…, 𝑠𝑗 ⟩ and 𝜎(𝑘)
(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,…, 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔
while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗<𝑖, in this case, 𝜎(𝑖..𝑗) = . Note that, 
denotes void (for nothing) and its length || is -1.
Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.
<PARSED TEXT FOR PAGE: 3 / 17>
Theoretical Computer Science 1049 (2025) 115368
3
Z. Duan, C. Tian, N. Zhang et al.
Fig. 1. Projected Intervals.
Fig. 2. Three cases of (𝑃1,…, 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)
𝜎1 ⋅ 𝜎2 =
⎧
⎪
⎪
⎨
⎪
⎪
⎩
𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ,
𝜎2, if 𝜎1 = ,
⟨𝑠0,…, 𝑠𝑖, 𝑠𝑖+1,…, 𝑠𝑗 ⟩, if 𝜎1 = ⟨𝑠0,…, 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,…, 𝑠𝑗 ⟩,
𝑗 ≤ 𝜔,|𝜎1| ≠ 𝜔.
It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1| + |𝜎2| and for any interval 𝜎,  ⋅ 𝜎 = 𝜎 ⋅  = 𝜎.
For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the
same successive state to produce different projected states, we define the projected interval:
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚) = ⟨𝑠𝑡0
, 𝑠𝑡1
,…, 𝑠𝑡𝑛
⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ …𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁, and 𝑡0, 𝑡1,…, 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,…, 𝑟𝑚 by deleting
all duplicates. That is, 𝑡0,…, 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,…, 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case,
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1, 𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected
intervals are given below (See Fig. 1).
(a) ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 3, 4, 4, 4, 6) = ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 4, 6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0, 0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47, 47, 𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47) = ⟨𝑠0, 𝑠21, 𝑠47⟩
Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1,…, 𝑃𝑚 are interpreted
in the projection construct. In order to interpret the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞
as follows:
Let 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠𝑚,…, 𝑠𝑗 ⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is
interpreted over a subinterval 𝜎(𝑟𝑖−1..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,…, 𝑠𝑟𝑖
⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination
of 𝑃𝑚 (see red color sequence).
Thus, we define 𝜎𝑞 as follows:
𝜎(𝑟𝑚+1..𝑗) =
{ < 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,
, if 𝑟𝑚 = 𝑗.
𝜎𝑞 = 𝜎 ↓ (𝑟0,…, 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)
<IMAGE FOR PAGE: 3 / 17>
![image](sediment://7a41b68aec6f5e2#file_00000000677c7209a156353e1c071784#p_2.jpg)
<PARSED TEXT FOR PAGE: 4 / 17>
Theoretical Computer Science 1049 (2025) 115368
4
Z. Duan, C. Tian, N. Zhang et al.
Table 1
Derived formulas.
A1 𝜀
def
= ¬ ○ ⊤ A2 𝜖def
= ○⊤
A3 ⨀𝑃 def
= 𝜀 ∨ ○𝑃 A4 𝑃 ;𝑄 def
= (𝑃,𝑄) 𝑝𝑟𝑗 𝜀
A5 ◊ 𝑃 def
= ⊤;𝑃 A6 □𝑃 def
= ¬◊¬𝑃
A7 𝑓 𝑖𝑛 def
= ◊𝜀 A8 𝑖𝑛𝑓 def
= ¬𝑓 𝑖𝑛
A9 {
○0𝑃 def
= 𝑃
○𝑛𝑃 def
= ○(○𝑛−1𝑃 )(𝑛 > 0)
A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧ 𝑄 ∨ 𝑃 ∧ (𝑄;⊤)
∨𝑃 ∧ 𝑄 ∧ □ 𝜖
A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)
𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.
PPTL formulas are interpreted over intervals. An interpretation  = (𝜎, 𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,…, 𝑠𝑗 ⟩ of 𝜎 with the current state
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎⊧𝑃
if 𝜎(0,|𝜎|) ⊧ 𝑃 .
(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.
(2)  ⊧ ○𝑃 iff 𝑘<𝑗 and (𝜎,𝑘 + 1, 𝑗) ⊧ 𝑃 .
(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .
(4)  ⊧ 𝑃 ∨ 𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.
(5)  ⊧ (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟�
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn4file2 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 ,
The file is too long and its contents have been truncated.


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
可以。第二节是整篇论文的**逻辑基础**，如果这一节没吃透，后面第 3 节的限界语义和 SAT 编码就会比较难。下面我按 **2.0 总述 → 2.1 语法 → 2.2 语义 → 2.3 范式** 的顺序，尽量按原文句子意思逐句讲。fileciteturn4file1

---

# 2. Propositional projection temporal logic

原文先说：

> 为了研究区间时序逻辑的限界模型检测，本文选择 **PPTL** 作为底层逻辑；下面简要介绍它的语法和语义。fileciteturn4file1

这句话的意思是：

- 这篇论文不是随便挑一个逻辑；
- 它要研究的是 **interval based temporal logic**，也就是**基于区间的时序逻辑**；
- 在这一类逻辑里，作者选择 **PPTL** 来描述系统性质；
- 第二节的作用，就是把后面要用到的 PPTL 基础符号统一说明。

你可以把这一节理解成：

> “先把游戏规则说清楚，后面第 3 节才能正式做 BMC。”

---

# 2.1 Syntax

这一小节是 **PPTL 的语法定义**。

---

### 句子 1

> PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. fileciteturn4file1

意思是：

- PPTL 建立在**命题逻辑**之上；
- 但它不是只会“与、或、非”；
- 它还有两个最原始的时序构造，用来描述**时间区间上的行为**。

这里“primitive”表示**原始基本算子**，后面很多常见时序算子都要从它们派生出来。

---

### 句子 2

> Let Prop be a countable set of atomic propositions, and $N$ the set of natural numbers. fileciteturn4file1

意思是：

- `Prop` 是原子命题集合，比如 $p,q,r$；
- `countable` 意味着可以有无限多个原子命题，但至少是可数的；
  - $N$ 是自然数集合，后面下标、重复次数、分段编号都要用到它。

---

### 句子 3：最重要的语法式

$
P ::= p \mid \circ P \mid \neg P \mid P_1 \vee P_2 \mid (P_1,\dots,P_m)\ prj\ P
$
fileciteturn4file1

这是 PPTL 公式的**归纳定义**，逐项解释：

#### 1）$p$
表示一个原子命题，比如“处理器空闲”“请求到达”“任务完成”。

#### 2）$\circ P$
这是 **next** 算子，表示“下一状态满足 $P$”。

#### 3）$\neg P$
普通逻辑非。

#### 4）$P_1 \vee P_2$
普通逻辑或。

#### 5）$(P_1,\dots,P_m)\ prj\ P$
这是 **projection（投影）** 算子，也是 PPTL 最核心、最难的地方。

直观地说，它表示：

- 先把当前区间切成若干段；
- 每一段分别满足 $P_1,\dots,P_m$；
- 再把这些分段的“端点”抽取出来，形成一个新的投影区间；
- 最后让 $P$ 在这个投影区间上成立。

你先记一句最直观的话：

> **prj 就是在原区间里先分段，再抽关键点，再在关键点构成的新区间上检查性质。**

---

### 句子 4
> where $p \in Prop$ and $P,P_1,\dots,P_m$ are well-formed PPTL formulas. fileciteturn4file1

这是在说：上面那个语法规则递归生成的表达式，都算是合法的 PPTL 公式。

---

### 句子 5
> PPTL formulas consist of two basic temporal operators: next $(\circ)$ and projection $(prj)$. fileciteturn4file1

这句话非常关键。

意思是：PPTL 真正的时序核心只有两个：

- **next**
- **projection**

后面你看到的 `;`、`◇`、`□`、`len(n)` 这些都不是原始算子，而是**派生定义**。

---

### 句子 6
> A formula is called a state formula if it contains no temporal operators, otherwise it is called a temporal formula. fileciteturn4file1

意思是：

- **状态公式**：不含时序算子，只描述“当前状态”；
  例如 $p$、$p\vee q$、$\neg p$
- **时序公式**：只要含有 $\circ$ 或 $prj$，就属于时序公式。

这个区分在 2.3 正规形里很重要，因为正规形里的 $Q_e,Q_i$ 都要求是**状态公式**。

---

# 2.2 Semantics

这一小节是最难的，因为它定义了 PPTL 公式到底“什么时候成立”。

---

## 第一组：基础数学对象

### 句子 1
> Let $B=\{\top,\bot\}$ be the set of boolean values. fileciteturn4file1

就是布尔真假集合。

---

### 句子 2
> Let $\omega$ denote infinity. We consider the extended integer set $N_\omega=N\cup\{\omega\}$. fileciteturn4file1

意思是：

- $\omega$ 表示“无限”；
- 作者把自然数集合扩展成 $N_\omega$，这样就能同时表示：
  - 有限位置 $0,1,2,\dots$
  - 无限终点 $\omega$

为什么要这样做？

因为 PPTL 的区间既可能是**有限区间**，也可能是**无限区间**。

---

### 句子 3
> and extend the comparison operators ... by considering $\omega=\omega$, and for all $i\in N$, $i<\omega$, $\omega=\omega+i$. Furthermore, we define $\preceq$ as $\le - \{(\omega,\omega)\}$. fileciteturn4file1

这句稍难，我给你拆开。

#### （1）$i<\omega$
任何有限整数都小于无穷。

#### （2）$\omega=\omega+i$
无限后面再加有限步，还是无限。

#### （3）定义 $\preceq$
这个符号和 $\le$ 很像，但**把 $(\omega,\omega)$** 这一种情况去掉了。

也就是：

- $a\preceq b$ 大体上表示“严格偏前或正常不超出”；
- 但不允许 $\omega\preceq\omega$

这个细节主要是为了后面 projection 里写
$
r_0\le r_1\le \cdots \preceq r_m\le j
$
时更严谨，避免某些无限端点上的退化情况。

你现在不用死抠它，先知道：

> $\preceq$ 是作者为了处理无限区间端点而专门引入的“弱于等于但排除 $(\omega,\omega)$”的关系。

---

## 第二组：状态与区间

### 句子 4
> A state $s_i$ is a mapping from Prop to $B$. fileciteturn4file1

意思是：

一个状态 $s_i$ 会告诉你每个原子命题是真是假。

比如：

- $s_i(p)=\top$
- $s_i(q)=\bot$

所以状态本质上是一个**真值赋值**。

---

### 句子 5
> An interval $\sigma$ is a finite or infinite sequence of states, denoted by $\sigma=\langle s_0,s_1,\dots,s_{|\sigma|}\rangle$. fileciteturn4file1

意思是：

PPTL 不像普通命题逻辑只看一个状态，它看的是**状态序列**，也就是区间。

这个区间可以是：

- 有限的：$\langle s_0,s_1,\dots,s_n\rangle$
- 无限的：$\langle s_0,s_1,\dots\rangle$

---

### 句子 6
> The length, $|\sigma|$, of $\sigma$ is $\omega$ if $\sigma$ is infinite, and the number of states minus 1 if $\sigma$ is finite. fileciteturn4file1

这个地方特别容易看错。

如果有限区间有 5 个状态：

$
\langle s_0,s_1,s_2,s_3,s_4\rangle
$

那它的长度不是 5，而是：

$
|\sigma|=4
$

也就是**最后一个下标**。

所以论文里的长度定义，本质上更像“最后位置编号”，不是状态个数。

---

### 句子 7
> An interval that contains only one state is called a singleton interval $\langle s_0\rangle$, and its length is 0. fileciteturn4file1

单状态区间长度为 0，这和“长度是最后下标”一致。

---

### 句子 8
> For convenience, we use notation $\sigma(i..j)$ to denote the subinterval $\langle s_i,\dots,s_j\rangle$ and $\sigma(k)$ to denote $\langle s_k,\dots,s_{|\sigma|}\rangle$. fileciteturn4file1

意思是：

- $\sigma(i..j)$：从第 $i$ 个状态到第 $j$ 个状态的子区间
- $\sigma(k)$：从第 $k$ 个状态一直到结尾

这和字符串切片很像。

---

### 句子 9
> It becomes an infinite interval $\sigma(i..\omega)=\langle s_i,\dots\rangle$ when $j=\omega$, while $\sigma(i..i)=\langle s_i\rangle$ becomes a singleton interval when $i=j$. fileciteturn4file1

就是把上面符号的特殊情况说清楚：

- 如果终点是 $\omega$，那就是无限后缀；
- 如果起点终点相同，就是单点区间。

---

### 句子 10
> In some circumstances, we allow $j<i$, in this case, $\sigma(i..j)=\varepsilon$. Note that, $\varepsilon$ denotes void and its length is -1. fileciteturn4file1

这一句非常重要。

这里的 $\varepsilon$ 不是公式，而是一个**空区间 / void interval**。

也就是说：

- 如果切片区间“反过来了”，比如从 5 到 3；
- 那定义结果为空区间 $\varepsilon$；
- 其长度规定为 $-1$

为什么这么做？

因为后面拼接、投影时会出现“后半段不存在”的情况，定义一个空区间会让公式写起来更统一。

注意这里有两个“epsilon”：

- **语义对象里的 $\varepsilon$**：空区间
- **表 1 里公式 A1 的 $\epsilon$**：表示“当前是最后一个状态”的公式

这两个长得像，但不是一回事。这个很关键。

---

## 第三组：区间拼接

### 句子 11
> Now, we present the concatenation $(\cdot)$ operation on intervals. fileciteturn4file1

就是定义区间怎么首尾接起来。

---

### 句子 12
> $\sigma_1\cdot \sigma_2$ is the interval whose states are the states of $\sigma_1$ followed by the states of $\sigma_2$. fileciteturn4file1

直观意思就是“前一段接后一段”。

但作者随后给了更精细的分情况定义。fileciteturn4file2

---

### 拼接的三种情况

#### 情况 1：$|\sigma_1|=\omega$ 或 $\sigma_2=\varepsilon$
结果就是 $\sigma_1$

意思：

- 如果前一段已经无限长了，后面没法再接；
- 或者后一段是空的，接了也没变化。

#### 情况 2：$\sigma_1=\varepsilon$
结果就是 $\sigma_2$

空区间作左单位元。

#### 情况 3：普通有限拼接
如果
$
\sigma_1=\langle s_0,\dots,s_i\rangle,\quad
\sigma_2=\langle s_{i+1},\dots,s_j\rangle
$
那么
$
\sigma_1\cdot\sigma_2=\langle s_0,\dots,s_i,s_{i+1},\dots,s_j\rangle
$

就是正常首尾拼起来。fileciteturn4file2

---

### 句子 13
> It is straightforward that $|\sigma_1\cdot\sigma_2|=|\sigma_1|+|\sigma_2|$ and for any interval $\sigma$, $\varepsilon\cdot\sigma=\sigma\cdot\varepsilon=\sigma$. fileciteturn4file2

作者说这是显然的，意思是：

- 长度满足加法；
- 空区间是拼接单位元。

---

## 第四组：投影区间 projected interval

这是第二节最核心的概念之一。

### 句子 14
> some states can repeatedly appear in the sequence (stutter). To avoid the same successive state to produce different projected states, we define the projected interval. fileciteturn4file2

意思是：

原区间里，某些位置可能重复出现，或者我们选择的端点序列里会有重复下标。  
为了不让这些重复点影响投影结果，作者专门定义了 **projected interval**。

---

### 定义式
$
\sigma \downarrow (r_0,r_1,\dots,r_m)=\langle s_{t_0},s_{t_1},\dots,s_{t_n}\rangle
$
其中 $t_0,\dots,t_n$ 是从 $r_0,\dots,r_m$ 里**删掉重复项后**得到的最长严格递增子序列。fileciteturn4file2

直观讲：

- 你先选出若干关键位置 $r_0,\dots,r_m$
- 再把重复位置删掉
- 最后取这些位置上的状态，形成一个新序列

这就是“投影区间”。

---

### 为什么要删重复

比如原文例子：

$
\langle s_0,\dots,s_8\rangle \downarrow (0,3,3,4,4,4,6)
= \langle s_0,s_3,s_4,s_6\rangle
$

这里 3 和 4 出现多次，但投影结果里只保留一次。fileciteturn4file2

你可以理解成：

> 投影只关心“关键端点有哪些”，不关心同一个端点被重复写了几次。

---

### 原文三个例子

#### 例 (a)
$
(0,3,3,4,4,4,6)\mapsto (0,3,4,6)
$
得到
$
\langle s_0,s_3,s_4,s_6\rangle
$

#### 例 (b)
$
\langle s_0,s_1,s_2\rangle \downarrow (0,0)=\langle s_0\rangle
$

#### 例 (c)
无限区间里如果最后写了 $\omega$，也会被忽略成前面的有限关键点序列。fileciteturn4file2

---

## 第五组：为什么定义 $\sigma_q$

### 句子 15
> Projected interval is obtained by taking the endpoints of the intervals over which $P_1,\dots,P_m$ are interpreted in the projection construct. fileciteturn4file2

意思是：

在
$
(P_1,\dots,P_m)\ prj\ Q
$
里，$P_1,\dots,P_m$ 是分别在若干子区间上解释的。  
这些子区间都有端点，把这些端点抽出来，就形成投影区间。

---

### 句子 16
> In order to interpret the formula $(P_1,\dots,P_m)\ prj\ Q$ intuitively, we need to work out a useful interval $\sigma_q$. fileciteturn4file2

这句话非常重要。

作者说：仅仅有端点还不够，因为 $Q$ 可能：

1. 在 $P_m$ 结束前就结束；
2. 和 $P_m$ 同时结束；
3. 在 $P_m$ 结束后还继续。

所以必须构造一个专门给 $Q$ 用的新区间 $\sigma_q$。

---

### 句子 17
> Let $\sigma$ be an interval ... while $P_i$ is interpreted over a subinterval $\sigma(r_{i-1}..r_i)$. fileciteturn4file2

意思是：

整个原区间是 $\sigma$，  
其中第 $i$ 段子区间
$
\sigma(r_{i-1}..r_i)
$
满足 $P_i$。

所以：

- $r_0,r_1,\dots,r_m$ 就是分段端点；
- 这些点同时也是“投影区间”的候选关键点。

---

### 句子 18
> There are three cases ... Case 1: $Q$ terminates before $P_m$, Case 2: $Q$ and $P_m$ terminate at the same state, and Case 3: $Q$ continues after the termination of $P_m$. fileciteturn4file2

这句话就是图 2 的核心。

也就是说，$Q$ 的解释区间可能有三种长度关系。  
所以 $\sigma_q$ 不能简单地只取端点，还要考虑 $P_m$ 结束后剩余的那段尾巴。

---

### 定义 $\sigma_q$

作者定义：
$
\sigma_q=\sigma\downarrow(r_0,\dots,r_m)\cdot \sigma(r_m+1..j)
$
fileciteturn4file2

直观解释：

- 前半部分：取 $P_1,\dots,P_m$ 各段的端点，形成投影区间；
- 后半部分：如果原区间在 $r_m$ 后还有剩余，就把这段尾巴接上。

所以 $\sigma_q$ 是由两部分拼起来的：

1. **关键端点投影**
2. **剩余后缀**

这就是为什么原文说 $\sigma_q$ 被分成两部分，会方便解释 prj 的 3 种情况。fileciteturn4file2

---

## 第六组：派生公式 Table 1

这一块不是原始定义，但非常常用。

---

### A1
$
\epsilon \overset{def}= \neg \circ \top
$
fileciteturn4file2

这表示：

> 当前已经是区间最后一个状态。

因为如果“下一步一定真”都不成立，说明已经没有下一步了。

---

### A2
$
\epsilon' \overset{def}= \circ \top
$
文中写成另一个 epsilon 变体，本质表示“存在下一状态”。fileciteturn4file2

---

### A3
$
\odot P \overset{def}= \epsilon \vee \circ P
$

意思是：

- 要么当前已经结束；
- 要么下一状态满足 $P$

有点像“弱 next”。

---

### A4
$
P;Q \overset{def}= (P,Q)\ prj\ \epsilon
$
fileciteturn4file2

这就是**顺序组合**。

直观意思：

> 先有一段满足 $P$，再有一段满足 $Q$，并且整个组合正好在这里结束。

这个算子后面会经常见到。

---

### A5
$
\Diamond P \overset{def}= \top;P
$

意思是：

> 当前开始，经过某段任意过程后，最终有一段满足 $P$

也就是“最终 $P$”。

---

### A6
$
\Box P \overset{def}= \neg \Diamond \neg P
$

就是“一直 $P$”。

---

### A7, A8
$
fin \overset{def}= \Diamond \epsilon,\qquad inf \overset{def}= \neg fin
$

分别表示：

- 有限区间
- 无限区间

---

### A9
$
\circ^0 P=P,\qquad \circ^n P=\circ(\circ^{n-1}P)
$

表示把 next 连续用 $n$ 次。

---

### A10
并行算子 $P\parallel Q$ 的定义。  
这个式子比较长，你现阶段只要知道：

> 它是在 PPTL 中定义“并行发生/重叠发生”的一种派生写法。

---

### A11
$
len(n)\overset{def}= \circ^n \epsilon
$

意思是：

> 区间长度正好为 $n$

比如：

- $len(0)$：当前就是最后一个状态
- $len(2)$：两步之后结束

这个定义特别能体现 PPTL 对“时长性质”的表达能力。fileciteturn4file2

---

## 第七组：真正的满足关系

这部分是在正式定义 PPTL 公式如何解释。fileciteturn3file5

### 句子 19
> An interpretation $I=(\sigma,k,j)$ is a subinterval $\langle s_k,\dots,s_j\rangle$ of $\sigma$ with the current state being $s_k$. fileciteturn4file2

意思是：

PPTL 的解释不是只给一个区间 $\sigma$，而是给一个三元组：

- 原区间 $\sigma$
- 当前起点 $k$
- 当前终点 $j$

也就是：我们正在看 $\sigma$ 中从 $s_k$ 到 $s_j$ 这一段。

---

### 句子 20
> The semantics ... is inductively defined as a satisfaction relation. fileciteturn4file2

意思是：下面 5 条就是递归语义定义。

---

### 语义 (1)
$
I\models p \iff s_k[p]=\top
$
fileciteturn3file5

意思最简单：

> 原子命题 $p$ 是否成立，只看当前状态 $s_k$。

---

### 语义 (2)
$
I\models \circ P \iff k<j \text{ and } (\sigma,k+1,j)\models P
$
fileciteturn3file5

意思是：

- 只有在当前区间还有下一状态时，next 才有意义；
- 然后把当前点往后移一位，继续判断 $P$。

这和 LTL 的 next 类似，但这里是区间版本。

---

### 语义 (3)
$
I\models \neg P \iff I\not\models P
$

普通否定。fileciteturn3file5

---

### 语义 (4)
$
I\models P\vee Q \iff I\models P \text{ or } I\models Q
$

普通析取。fileciteturn3file5

---

### 语义 (5)：projection 的正式定义

$
I\models (P_1,\dots,P_m)\ prj\ Q
$
当且仅当存在
$
k=r_0\le r_1\le \cdots \le r_{m-1}\preceq r_m\le j
$
使得：

1. 对每个 $l=1,\dots,m$，都有
   $
   (\sigma,r_{l-1},r_l)\models P_l
   $
2. 并且 $\sigma_q\models Q$ fileciteturn3file5turn3file2

这是整节最关键的定义。

我把它翻成大白话：

> 在当前区间 $\sigma(k..j)$ 里，能找到一组分割点  
> $r_0,r_1,\dots,r_m$，  
> 使得每一段都分别满足 $P_1,\dots,P_m$，  
> 然后把这些端点投影并接上必要尾部得到 $\sigma_q$，  
> 再要求 $Q$ 在 $\sigma_q$ 上成立。

这就是 projection 的完整语义。

---

## 第八组：satisfiable / valid

### 句子 21
> A formula $p$ is satisfied by an interval $\sigma$, denoted $\sigma\models p$, if $(\sigma,0,|\sigma|)\models p$. fileciteturn3file5

意思是：

如果不特别说明起点终点，默认就是**整个区间**上判断公式。

---

### 句子 22
> satisfiable if $\sigma\models p$ for some $\sigma$. valid if $\sigma\models p$ for all $\sigma$. fileciteturn3file5

- **可满足**：至少存在一个区间使它成立
- **有效**：所有区间都成立

和一般逻辑中的 satisfiable / valid 一样。

---

# 2.3 Normal form

这一小节是在为第 3 节做准备。

---

### 句子 1
> Normal Form (NF) is a useful notation in our methods. fileciteturn3file2

意思是：

正规形不是为了好看，而是为了后面做 BMC 和 SAT 编码时方便递归处理。

---

### 句子 2
> We assume $Q_p$ is the set of atomic propositions appearing in formula $Q$. fileciteturn3file2

就是一个符号约定：$Q_p$ 表示公式 $Q$ 中出现的原子命题集合。

---

### 句子 3：正规形定义
$
NF(Q)\equiv \bigvee_j(Q_{e_j}\land \epsilon)\ \vee\ \bigvee_i(Q_{c_i}\land \circ Q_i')
$
fileciteturn3file2

意思是：任意 PPTL 公式都可以改写成两类分支的析取：

#### 第一类
$
Q_{e_j}\land \epsilon
$

表示：

- 当前满足某个状态条件 $Q_{e_j}$
- 并且当前就是区间末尾

#### 第二类
$
Q_{c_i}\land \circ Q_i'
$

表示：

- 当前满足某个状态条件 $Q_{c_i}$
- 并且下一步以后满足 $Q_i'$

这非常像“自动机一步展开”的结构。

---

### 句子 4
作者又把它简写成：
$
NF(Q)\equiv Q_e\land \epsilon \ \vee\ \bigvee_{i=1}^r(Q_i\land \circ Q_i')
$
其中 $Q_e,Q_i$ 都是状态公式。fileciteturn3file2

简化之后就更好记了：

> 一个 PPTL 公式，要么“现在结束”，要么“现在满足某条件并跳到下一步继续”。

这就是后面 bounded semantics 能递归编码的原因。

---

### 句子 5
> Any PPTL formula can be rewritten into its Normal Form. fileciteturn3file2

意思是：

正规形不是只对部分公式有效，而是对**任意 PPTL 公式**都成立。

这给后面第 3 节一个巨大简化：

> 不用对所有复杂公式逐类定义限界语义，只要处理正规形即可。

---

### 句子 6：例子
论文给了
$
f\equiv (p;q)\ prj\ r
$
的正规形展开。fileciteturn3file4turn3file10

你现阶段不用硬背它的每一项，但要理解它想说明什么：

- 原本一个带 `;` 和 `prj` 的复杂公式；
- 经过正规形化之后；
- 被拆成若干个“当前状态条件 + 是否结束 / 下一步继续”的析取项。

也就是说：

> 正规形把复杂的区间时序结构，统一压扁成了适合递归求解的局部结构。

---

# 第二节整体到底想传达什么

你可以把第二节压缩成 4 句话：

1. **PPTL 是区间时序逻辑**，原始时序算子只有 `next` 和 `projection`。fileciteturn4file1
2. **公式是在区间上解释的**，区间可以有限也可以无限，还定义了子区间、拼接、投影区间。fileciteturn4file1turn4file2
3. **projection 的本质**是：先分段满足 $P_1,\dots,P_m$，再抽端点构成 $\sigma_q$，再让 $Q$ 在 $\sigma_q$ 上成立。fileciteturn3file5turn4file2
4. **任意 PPTL 公式都能化成正规形**，这为第 3 节的限界语义和 SAT 归约铺平了路。fileciteturn3file2turn3file4

---

# 你现在最应该真正弄懂的 3 个点

第一，**区间不是路径位置，而是一段状态序列**。\
第二，**prj 不是普通连接词，它会“分段 + 抽端点 + 重建区间”**。\
第三，**正规形就是把复杂公式化成“结束项 or 继续项”**。

---

接下来你要是继续，我建议直接讲 **2.2 里 projection 语义的一个具体例子**，我可以不用抽象符号，给你手动画式地讲明白 $(P_1,P_2)\ prj\ Q$ 到底是怎么判断真的。


#### You:
这里的P和Q是投影的意思吗

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
不是。这里的 **$P$** 和 **$Q$** 不是“投影”本身，它们都是 **公式**；真正表示“投影操作”的，是中间那个 **`prj`**。fileciteturn3file5

更准确地说，在公式

$
(P_1,\dots,P_m)\ prj\ Q
$

里：

- $P_1,\dots,P_m$：是**前面若干段区间上要满足的公式**
- `prj`：是**投影算子**
- $Q$：是**在投影出来的新区间上要满足的公式**。fileciteturn4file1turn3file5

你可以把它理解成三步：

### 1. 先分段
把原区间分成几段：

$
\sigma(r_0..r_1),\ \sigma(r_1..r_2),\ \dots,\ \sigma(r_{m-1}..r_m)
$

要求这些段分别满足：

$
P_1,\ P_2,\ \dots,\ P_m
$

也就是说，**$P_i$ 是“每一段上的条件”**。fileciteturn3file5

### 2. 再做投影
把这些分段的端点 $r_0,r_1,\dots,r_m$ 抽出来，构成一个新的区间 $\sigma_q$。这一步才叫“投影”。fileciteturn4file2turn3file5

### 3. 最后检查 $Q$
要求公式 $Q$ 在这个新得到的投影区间 $\sigma_q$ 上成立。  
所以 **$Q$ 不是投影**，而是**投影后的目标性质**。fileciteturn3file5

---

## 一个最直观的说法

$
(P_1,P_2)\ prj\ Q
$

不是说“P 和 Q 都表示投影”，而是说：

> 原区间先找两段，第一段满足 $P_1$，第二段满足 $P_2$；  
> 然后把这两段的关键端点抽出来；  
> 再看抽出来的新区间是否满足 $Q$。

所以：

- **$P_1,P_2$**：像“前置分段条件”
- **$Q$**：像“投影后的检查条件”
- **`prj`**：才是“投影这个动作”

---

## 你容易混淆的点

之所以会觉得 $P$ 和 $Q$ 都像“投影”，是因为它们都出现在 `prj` 公式里。  
但它们扮演的角色不同：

- 前面的 $P_i$：决定**怎么切原区间**
- 后面的 $Q$：决定**投影后的新区间要满足什么**

---

## 类比一下

你可以把它想成：

- $P_1,\dots,P_m$：是“筛选原视频里哪些片段”
- `prj`：是“把这些片段的关键帧抽出来”
- $Q$：是“检查抽出来的新短视频是否满足某个性质”

---

一句话说清楚：

> **$P_i$ 和 $Q$ 都是公式，不是投影；`prj` 才是投影算子。前面的 $P_i$ 用来分段，后面的 $Q$ 用来约束投影后的新区间。**

你要的话，我下一条可以直接用一个长度 4 的具体状态序列，手把手演示  
$
(P_1,P_2)\ prj\ Q
$
到底是怎么判断成立的。


#### You:
![image](sediment://file_00000000b8ac7209b00a430484cee489)
仔细讲讲2.3正规型

#### ChatGPT:
\[Unsupported Content]


#### Plugin (file_search):
Make sure to include fileciteturn6file0 in your response to cite this file, or to surface it as a link.
<PARSED TEXT FOR PAGE: 1 / 17>
Theoretical Computer Science 1049 (2025) 115368
Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.
Contents lists available at ScienceDirect
Theoretical Computer Science
journal homepage: www.elsevier.com/locate/tcs
SAT-based bounded model checking for propositional projection
temporal logic ✩
Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a
a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China b China Academy of Space Technology, Beijing 100094, China
A R T I C L E I N F O A B S T R A C T
Section Editor: Paul G. Spirakis
Handling Editor: Ding-Zhu Du
Keywords:
Propositional projection temporal logic
Bounded model checking
Rate monotonic scheduling
This paper presents a bounded model checking (BMC) approach for propositional projection
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed
in the paper is useful and feasible.
1. Introduction
Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted,
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware,
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀⊧𝜙?). With temporal logics, linear-time temporal
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8]
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9].
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC)
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs.
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC
✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.
* Corresponding authors.
E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn
(C. Yu), yangmf@bice.org.cn (M. Yang).
https://doi.org/10.1016/j.tcs.2025.115368
Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025
<PARSED TEXT FOR PAGE: 2 / 17>
Theoretical Computer Science 1049 (2025) 115368
2
Z. Duan, C. Tian, N. Zhang et al.
is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥.
As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors
such as EBMC [20] are used in the verification of large-scale hardware and software systems.
Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.
With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach,
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.
The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the
conclusion is drawn in section 8.
2. Propositional projection temporal logic
To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL)
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to
[26].
2.1. Syntax:
PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:
𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗 𝑃
where 𝑝 ∈ 𝑃 𝑟𝑜𝑝 and 𝑃,𝑃1,…, 𝑃𝑖,…, 𝑃𝑙,…, 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙, 𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal
operators, otherwise it is called a temporal formula.
2.2. Semantics:
Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 = 𝑁 ∪ {𝜔} and extend
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁, 𝑖 < 𝜔, 𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as
≤ −{(𝜔,𝜔)}.
A state 𝑠𝑖 is a mapping from 𝑃 𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,…, 𝑠|𝜎|⟩.
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote
the subinterval ⟨𝑠𝑖,…, 𝑠𝑗 ⟩ and 𝜎(𝑘)
(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,…, 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔
while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗<𝑖, in this case, 𝜎(𝑖..𝑗) = . Note that, 
denotes void (for nothing) and its length || is -1.
Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.
<PARSED TEXT FOR PAGE: 3 / 17>
Theoretical Computer Science 1049 (2025) 115368
3
Z. Duan, C. Tian, N. Zhang et al.
Fig. 1. Projected Intervals.
Fig. 2. Three cases of (𝑃1,…, 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)
𝜎1 ⋅ 𝜎2 =
⎧
⎪
⎪
⎨
⎪
⎪
⎩
𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ,
𝜎2, if 𝜎1 = ,
⟨𝑠0,…, 𝑠𝑖, 𝑠𝑖+1,…, 𝑠𝑗 ⟩, if 𝜎1 = ⟨𝑠0,…, 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,…, 𝑠𝑗 ⟩,
𝑗 ≤ 𝜔,|𝜎1| ≠ 𝜔.
It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1| + |𝜎2| and for any interval 𝜎,  ⋅ 𝜎 = 𝜎 ⋅  = 𝜎.
For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the
same successive state to produce different projected states, we define the projected interval:
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚) = ⟨𝑠𝑡0
, 𝑠𝑡1
,…, 𝑠𝑡𝑛
⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ …𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁, and 𝑡0, 𝑡1,…, 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,…, 𝑟𝑚 by deleting
all duplicates. That is, 𝑡0,…, 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,…, 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case,
𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1, 𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,…, 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected
intervals are given below (See Fig. 1).
(a) ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 3, 4, 4, 4, 6) = ⟨𝑠0,…, 𝑠8⟩ ↓ (0, 3, 4, 6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0, 0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47, 47, 𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0, 21, 47) = ⟨𝑠0, 𝑠21, 𝑠47⟩
Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1,…, 𝑃𝑚 are interpreted
in the projection construct. In order to interpret the formula (𝑃1,…, 𝑃𝑚) 𝑝𝑟𝑗
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn6file1 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 , 𝑠𝑡1 ,… , 𝑠𝑡𝑛 ⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ … 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁 , and 𝑡0, 𝑡1,… , 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,… , 𝑟𝑚 by deleting 
all duplicates. That is, 𝑡0,… , 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,… , 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case, 
𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1,𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected 
intervals are given below (See Fig. 1).

(a) ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,3,4,4,4,6) = ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,4,6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0,0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47,47,𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47) = ⟨𝑠0, 𝑠21, 𝑠47⟩

Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1 ,… , 𝑃𝑚 are interpreted 
in the projection construct. In order to interpret the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞

as follows:

Let 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠𝑚,… , 𝑠𝑗�
The file is too long and its contents have been truncated.


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
可以，这一小节值得仔细讲。**2.3 正规型（Normal Form, NF）** 是整篇论文从“复杂 PPTL 公式”走向“可做限界语义、可做 SAT 编码”的桥梁。作者先给出 NF 的定义，再说明任意 PPTL 公式都能化成这种形式，最后给一个例子 $f \equiv (p;q)\ prj\ r$。fileciteturn5file6

---

## 一、先说结论：正规型到底是什么

作者把任意 PPTL 公式 $Q$ 写成下面这种统一结构：

$
NF(Q)\equiv \bigvee_{j=1}^{n_0}(Q_{e_j}\land \varepsilon)\ \vee\ \bigvee_{i=1}^{n}(Q_{c_i}\land \circ Q_i')
$

然后又把它简写为：

$
NF(Q)\equiv Q_e\land \varepsilon\ \vee\ \bigvee_{i=1}^{r}(Q_i\land \circ Q_i')
$

其中 $Q_e$ 和 $Q_i$ 都是**状态公式**。fileciteturn5file6

这两式是同一个意思，简写版只是把“很多个结束项”合并成一个 $Q_e$，把“很多个继续项”统一写成 $Q_i$。

---

## 二、这两个部分分别是什么意思

这个式子最重要的不是背下来，而是看懂它在说什么。

### 第一部分：$Q_e \land \varepsilon$

它表示：

- 当前状态满足某个**状态条件** $Q_e$
- 并且当前已经到达**区间末尾**，即 $\varepsilon$

所以这一类项可以理解成：

> **“现在就结束。”**

---

### 第二部分：$\bigvee_{i=1}^{r}(Q_i\land \circ Q_i')$

它表示：

- 当前状态满足某个**状态条件** $Q_i$
- 然后“下一步”开始，剩下的区间要满足 $Q_i'$

所以这一类项可以理解成：

> **“现在不结束，下一步继续检查。”**

---

## 三、为什么这种形式很重要

因为它把一个复杂时序公式统一拆成了两种最基本的局部情况：

1. **结束型**：当前满足条件，并且到尾了  
2. **递进型**：当前满足条件，然后递归到下一步

也就是说，正规型把复杂的区间逻辑都压扁成了：

> **当前看什么 + 要不要往下一步走**

这正好适合后面第 3 节去定义**限界语义**和做**SAT 递归编码**。论文也明确说，因为每个 PPTL 公式都能化成 NF，所以后面不需要针对所有复杂公式逐类讨论，只需考虑含 $\vee,\neg,\circ$ 以及 $\varepsilon,\epsilon'$ 的形式。fileciteturn5file4turn5file9

---

## 四、逐句解释定义部分

### 1. “Normal Form (NF) is a useful notation in our methods.”

意思是：  
正规型不是单纯为了写得整齐，而是**作者方法中的核心工具**。后面很多推导都默认先把公式变成 NF。fileciteturn5file6

---

### 2. “We assume $Q_p$ is the set of atomic propositions appearing in the PPTL formula $Q$.”

这里的 $Q_p$ 只是一个记号，表示：

> 公式 $Q$ 中出现过的所有原子命题的集合。

比如如果
$
Q=(p;q)\ prj\ r
$
那 $Q_p=\{p,q,r\}$。

这一句本身在后面的定义里没有直接运算作用，更像是做符号准备。fileciteturn5file6

---

### 3. “Then, the NF can be defined as follows”

接下来就是 Definition 1，也就是上面那个正规型公式。fileciteturn5file6

---

## 五、定义 1 的每个符号怎么理解

### 1. $\bigvee$
表示“大析取”，就是很多个“或”。

### 2. $Q_{e_j}\land \varepsilon$
这是第 $j$ 个“结束分支”：

- $Q_{e_j}$：当前状态必须满足的布尔条件
- $\varepsilon$：当前就是最后一个状态

### 3. $Q_{c_i}\land \circ Q_i'$
这是第 $i$ 个“继续分支”：

- $Q_{c_i}$：当前状态的条件
- $\circ Q_i'$：下一状态开始满足 $Q_i'$

### 4. 为什么前面是 $Q_{e_j}$，后面是 $Q_{c_i}$
你可以记成：

- $e$ = end，结束
- $c$ = continue，继续

虽然论文没这样明说，但这样记最直观。

---

## 六、为什么作者又写了一个简化版

论文说：

> 为了简化证明和表达，有时用 $Q_e\land\varepsilon$ 代替 $\bigvee_{j=1}^{n_0}(Q_{e_j}\land\varepsilon)$，并用 $\bigvee_{i=1}^{r}(Q_i\land\circ Q_i')$ 代替原来的第二部分。fileciteturn5file6

这句话的真实含义是：

### 原始写法
$
\bigvee_{j=1}^{n_0}(Q_{e_j}\land \varepsilon)
$
表示可能有很多种“结束方式”。

### 简化写法
$
Q_e\land \varepsilon
$
其中 $Q_e$ 本身就可以是一个析取状态公式，例如：

$
Q_e = Q_{e_1}\vee Q_{e_2}\vee \cdots \vee Q_{e_{n_0}}
$

所以把很多结束项合并成一个状态公式 $Q_e$ 完全没问题。

同理，继续项也只是换了记号，更方便写。fileciteturn5file6

---

## 七、为什么要求 $Q_e$ 和 $Q_i$ 是状态公式

论文特别写了：

> where $Q_e$ and $Q_i$ are state formulas. fileciteturn5file6

这句话非常关键。

因为这意味着：

- 正规型里，**当前时刻要检查的部分**，必须是不含时序算子的纯状态条件；
- 真正的“时间推进”只体现在 $\circ Q_i'$ 里。

换句话说，正规型把“当前”和“未来”严格分开了：

- 当前：只看状态公式 $Q_e,Q_i$
- 未来：统一交给下一步的 $Q_i'$

这正是它适合递归处理的原因。

---

## 八、定理 1 到底说明了什么

论文接着说：

> Any PPTL formula $P$ can be rewritten into its Normal Form. fileciteturn5file6

意思是：

> **正规型不是只适用于某些特殊公式，而是对所有 PPTL 公式都成立。**

这句话非常重要。因为如果只有部分公式能正规化，那后面的 BMC 只能处理一部分性质；但现在作者说**任意 PPTL 公式都能改写成 NF**，所以他们的后续方法理论上适用于整个 PPTL。fileciteturn5file6

---

## 九、你可以把正规型类比成“自动机一步展开”

这是理解 NF 的最好方式之一。

正规型：

$
NF(Q)\equiv Q_e\land \varepsilon\ \vee\ \bigvee_{i=1}^{r}(Q_i\land \circ Q_i')
$

很像在说：

- 要么当前就进入“接受/终止”情形；
- 要么满足某个条件，然后转移到下一个子公式继续检查。

这和自动机里的“接受状态 + 转移边”很像。  
所以正规型本质上是在把 PPTL 公式写成一种**一步可展开的递归结构**。

---

## 十、为什么第 3 节特别依赖正规型

论文在进入第 3 节时明确说：

> 因为每个 PPTL 公式都能转成等价的 NF，不像 LTL/CTL 那样要分别处理很多种算子，所以 bounded semantics 里只需要考虑很少几类公式。fileciteturn5file4

这句话的意思是：

- 原始 PPTL 里有 `prj`、`;`、`\Diamond`、`\Box` 等复杂构造；
- 但先正规化后，就只剩“结束项”和“next 递归项”；
- 于是限界语义和 SAT 编码就能统一递归写。

所以 2.3 不是附属内容，而是整篇算法真正能成立的前提之一。

---

# 十一、仔细讲 Example 1

论文给的例子是：

$
f \equiv (p;q)\ prj\ r
$

并给出：

$
NF(f)\equiv (r\land q\land p\land \varepsilon)
\vee (r\land p\land \circ(\top;q))
\vee (r\land q\land p\land \circ \top)
\vee (r\land p\land \circ(\top;(q;\top)))
$

fileciteturn5file6

这个例子看起来很跳，但其实它是在告诉你：

> 原来一个带 `;` 和 `prj` 的复杂公式，最后也能被拆成若干个“当前状态条件 + 下一步递归”的分支。

下面我把它慢慢拆开。

---

## 十二、先看原公式 $f \equiv (p;q)\ prj\ r$

这里：

- $p;q$ 表示“先 $p$，后 $q$”
- 再通过 `prj` 投影
- 最后要求投影后的区间满足 $r$

直观上，这个公式表示一种“先有 $p$ 段，再有 $q$ 段，投影后还要满足 $r$”的区间行为。

---

## 十三、为什么它的 NF 会有四项

因为作者是在枚举这个公式从“当前状态”看过去的几种可能局部形态。

你可以把这四项理解成四种分支：

---

### 第 1 项
$
r\land q\land p\land \varepsilon
$

意思是：

- 当前状态同时满足 $r,q,p$
- 并且当前已经到末尾

这表示一种**立即结束**的情况。  
也就是原公式在当前这个单点或终点处就已经能成立。fileciteturn5file6

---

### 第 2 项
$
r\land p\land \circ(\top;q)
$

意思是：

- 当前状态满足 $r\land p$
- 下一步开始满足 $(\top;q)$

这里 $\top;q$ 可以理解成：

> 先来一段任意行为，再进入 $q$

所以这一项表达的是：

> 当前先把 $p$ 和 $r$ 这部分拿到，剩下的 $q$ 部分留给后面去完成。fileciteturn5file6

---

### 第 3 项
$
r\land q\land p\land \circ\top
$

意思是：

- 当前满足 $r,q,p$
- 并且下一步只要求 $\top$，即任意

这可以理解成一种“关键条件已经在当前点凑齐，后面怎么走都行”的情况。fileciteturn5file6

---

### 第 4 项
$
r\land p\land \circ(\top;(q;\top))
$

意思是：

- 当前满足 $r\land p$
- 但后面要经过更长的一段结构，最终把 $q$ 放到中间完成

这是一种比第 2 项更“拉长”的继续情形。fileciteturn5file6

---

## 十四、这个例子最该学到什么

你不需要现在就把这四项的推导过程完全背出来，但一定要看懂它想说明的事：

### 核心不是“这四项怎么死算出来”
而是：

> **复杂公式可以拆成有限个局部分支，每个分支都符合 NF 模板。**

也就是：

- 有的分支是“当前结束”
- 有的分支是“当前满足一些状态条件，下一步继续”

这才是 Example 1 的真正目的。fileciteturn5file6

---

## 十五、把正规型翻成最朴素的话

任意 PPTL 公式 $Q$ 的正规型都在说：

> 从当前状态看，  
> 要么这就是最后一步，并且当前满足某个状态条件；  
> 要么当前满足某个状态条件，然后把剩下的任务交给下一步。

所以你以后只要看到

$
NF(Q)\equiv Q_e\land \varepsilon \vee \bigvee_i(Q_i\land \circ Q_i')
$

就直接在脑子里翻译成：

> **“结束，或者推进。”**

---

## 十六、为什么正规型特别适合 BMC

BMC 本来就是按步展开的：

- 第 0 步
- 第 1 步
- 第 2 步
- …
- 到第 $k$ 步

而正规型恰好也是按“当前 / 下一步”组织的，所以非常适合把公式写成递归布尔约束：

- 如果当前是最后一步，就走 $Q_e\land\varepsilon$
- 如果当前不是最后一步，就走某个 $Q_i\land\circ Q_i'$

  于是自然能翻译成 SAT 里的逐步展开公式。论文后面正是这么做的。fileciteturn5file4turn5file9

---

## 十七、你做汇报时可以这样讲 2.3

你可以直接用下面这段：

**2.3 正规型的作用是把任意 PPTL 公式统一写成“结束项 + 继续项”的析取形式。结束项写成 $Q\_e\land\varepsilon$，表示当前满足某个状态条件且区间到末尾；继续项写成 $Q\_i\land\circ Q\_i'$，表示当前满足某个状态条件，下一步继续检查子公式。由于任意 PPTL 公式都能化成正规型，后续限界语义和 SAT 编码就不必逐个处理复杂算子，而只需围绕这种统一结构递归展开。** fileciteturn5file6turn5file4

---

## 十八、最后帮你抓住 3 个最重要的点

第一，**正规型不是语义变了，而是等价改写**。\
第二，**正规型把复杂公式统一成“结束/继续”两类**。\
第三，**第 3 节能做 bounded semantics 和 SAT 规约，靠的就是这个统一结构**。fileciteturn5file6turn5file4

---

你要是继续，我下一步可以专门做两件事中的一个：\
**一种是把 Example 1 这四项逐项推导出来**，另一种是**直接讲“2.3 怎么服务于第 3.1 的限界语义定义”**。


#### You:
为什么example1是这么计算的？是否具有普遍性？

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
有，而且要分开看：

1. **为什么 Example 1 会算成那四项**
2. **这种“算成 NF”的做法有没有普遍性**

先说结论：

- **Example 1 那四项不是拍脑袋写出来的**，而是把\
  $
  f\equiv (p;q)\ prj\ r
  $
  按 **PPTL 的语义** 和 **正规型展开规则**，拆成“当前结束”或“当前继续”的几种局部情形。fileciteturn7file7turn7file6
- **它具有普遍性**，不是这个例子特有。论文的 **Theorem 1** 明确说：**任意 PPTL 公式都可以改写成正规型**。只是这篇论文没有在正文里给出这个定理的证明，而是说证明见文献 \[26]。fileciteturn7file6

下面我仔细讲。

---

# 一、先看 Example 1 原式到底是什么

论文给的例子是：

$
f\equiv (p;q)\ prj\ r
$

并给出：

$
NF(f)\equiv (r\land q\land p\land \varepsilon)\vee(r\land p\land \circ(\top;q))
\vee(r\land q\land p\land \circ\top)\vee(r\land p\land \circ(\top;(q;\top)))
$

这是论文原文直接给出的结果。fileciteturn7file6

这里要先提醒你一个关键点：

**这个例子没有把中间推导过程写出来。**  
论文只给了“结果”，没有给“逐步化简链”。所以我们现在能做的是：

- 根据前面 2.2 的 **projection 语义**
- 结合 Table 1 里 **顺序算子 `;` 的定义**
- 再结合 2.3 的 **NF 结构**
- 去反推为什么会出现这四类项

这一点我必须说清楚，避免假装论文里已经把每一步都写出来了。论文正文只给了结论，没给展开证明。fileciteturn7file5turn7file6

---

# 二、先把 $p;q$ 换成它真正的定义

在 Table 1 中，顺序算子定义为：

$
P;Q \overset{def}= (P,Q)\ prj\ \epsilon
$

也就是：

$
p;q \equiv (p,q)\ prj\ \epsilon
$

这里的意思是：

- 先有一段满足 $p$
- 再有一段满足 $q$
- 并且投影出来的区间满足 $\epsilon$，也就是“正好在这里结束”fileciteturn7file5

所以原式其实等价于：

$
((p,q)\ prj\ \epsilon)\ prj\ r
$

虽然论文没把它显式写成这一层套这一层，但从定义上就是这个意思。fileciteturn7file5turn7file7

---

# 三、NF 为什么一定会长成“结束项 or 继续项”

2.3 里正规型统一写成：

$
NF(Q)\equiv Q_e\land \varepsilon \vee \bigvee_{i=1}^{r}(Q_i\land \circ Q_i')
$

其中 $Q_e,Q_i$ 都是状态公式。fileciteturn7file6

这说明任何公式在当前时刻看，都只能分成两类：

### 第一类：现在就结束
形如
$
\text{状态条件}\land \varepsilon
$

### 第二类：现在不结束，下一步继续
形如
$
\text{状态条件}\land \circ(\text{剩余公式})
$

所以 Example 1 的那四项，本质上是在列举：

> 对于 $(p;q)\ prj\ r$，当前这一刻可能出现哪些“结束/继续”分支？

---

# 四、为什么会出现“$r$”几乎在每一项前面

因为最外层是

$
(\cdots)\ prj\ r
$

根据 projection 的语义：

$
\mathcal I \models (P_1,\dots,P_m)\ prj\ Q
$

当且仅当存在分段点，使前面的各段满足 $P_1,\dots,P_m$，并且投影出来的区间 $\sigma_q$ 满足 $Q$。fileciteturn7file7

现在这里的 $Q$ 就是原子命题 $r$。  
而原子命题的语义是：

$
(\sigma,k,j)\models r \iff s_k[r]=\top
$

也就是说，只要要求“投影区间满足 $r$”，本质上就是要求**投影区间的当前第一个状态满足 $r$**。fileciteturn7file7

而投影区间的第一个状态正对应原区间当前起点，所以你会看到 NF 的每个分支里都带着 $r$。这很正常。

你可以把它理解为：

> 不管后面怎么分段、怎么投影，既然最外层要求投影区间上立刻满足 $r$，那当前起点必须先满足 $r$。

---

# 五、为什么会有“$p$”几乎在每一项前面

因为里层有 $p;q$。

而 $p;q$ 的含义是：

- 当前开始的第一段要满足 $p$
- 后面第二段要满足 $q$
- 并且顺序组合按定义通过 projection 结束在合适位置fileciteturn7file5turn7file7

由于第一段是从当前起点开始，所以当前起点必须先满足 $p$。因此在 Example 1 的各个 NF 分支里，$p$ 也几乎总是出现。

---

# 六、那四项到底怎么来的：直观拆解

下面给你讲“为什么是这四项”，但我先说明：

> 这是根据语义做的**结构性反推解释**，不是论文正文逐行演算，因为正文没有给出中间步骤。fileciteturn7file6

---

## 第 1 项
$
r\land q\land p\land \varepsilon
$

这表示：

- 当前起点满足 $r$
- 当前也满足 $p$ 和 $q$
- 并且当前已经到区间末尾 $\varepsilon$

为什么会有这种项？

因为在 PPTL 的 projection/sequence 语义里，分段端点允许重合，即
$
r_0\le r_1\le \cdots \le r_m
$
不要求严格小于。fileciteturn7file7

所以：

- $p$ 那一段
- $q$ 那一段

都可能退化到当前这个终点上。  
这样整个公式就在“当前且结束”这一种极端情形下成立，于是出现了这一项。

你可以把它理解成：

> **所有任务都在最后这个点上一次性满足。**

---

## 第 2 项
$
r\land p\land \circ(\top;q)
$

它表示：

- 当前已经满足 $r\land p$
- 但 $q$ 还没有在当前点完成
- 所以下一步开始，剩下的结构要满足 $(\top;q)$

这里的 $\top;q$ 可以看成：

> 先允许往前走一段任意行为，再把 $q$ 这一段完成

为什么会出来这一项？

因为在 $p;q$ 的顺序结构里，当前点只够确认“第一段的起始条件 $p$ 已经到位”，而“后续的 $q$ 段”还要交给未来。所以正规型就会把它写成：

$
\text{当前状态条件} \land \circ(\text{剩余任务})
$

这正符合 NF 的第二部分模板。fileciteturn7file6

---

## 第 3 项
$
r\land q\land p\land \circ\top
$

它表示：

- 当前已经满足 $r,p,q$
- 下一步之后不再有实质性约束，只要求 $\top$

为什么会有这一项？

因为在某些分段方式下，**关键逻辑要求已经在当前点全部满足**，但从 NF 角度它仍属于“继续型”而不是“结束型”，于是后面的剩余公式就退化成最弱约束 $\top$。

也就是：

> 现在核心条件都凑齐了，后面怎么走都行。

---

## 第 4 项
$
r\land p\land \circ(\top;(q;\top))
$

这是最“拖尾”的一种情况。

它表示：

- 当前只有 $r\land p$ 确认了
- 后面还要经过更长的顺序结构
- 才能把 $q$ 那一段安放进去

为什么不是只有第 2 项就够了？

因为顺序 + 投影的组合不是单一一步结构，它有不同的“剩余区间形态”。  
有的情形是“很快就进入 $q$”，对应第 2 项；  
有的情形是“中间还要拉出一个更长的尾部结构”，于是剩余公式变成 $\top;(q;\top)$。

换句话说：

> Example 1 的四项，不是四个随便拼的公式，而是在枚举这个复合公式从当前往后可能出现的不同剩余形态。

---

# 七、为什么它不是三项、五项，而正好四项

本质原因是：

- 这个公式不算特别简单，因为同时包含了 **`;`** 和 **`prj`**
- 在正规化时，会把“当前满足什么”和“剩余结构是什么”拆开
- 而对于 $(p;q)\ prj\ r$ 这个具体公式，作者整理后恰好得到四个互补的分支

这四项合起来，完整覆盖了该公式在当前一步的所有可能局部展开。  
这和自动机一步展开时“列出所有可行转移分支”很像。

---

# 八、它有没有普遍性？有，但要区分两个层面

## 层面 1：**“能化成 NF”** 这件事有普遍性

这个是**有**的，而且论文明确给了定理：

> **Any PPTL formula $P$ can be rewritten into its Normal Form.** fileciteturn7file6

所以：

- 不是只有 Example 1 可以这样化
- 任何 PPTL 公式都可以化成
  $
  Q_e\land \varepsilon \vee \bigvee_i(Q_i\land \circ Q_i')
  $

这个普遍性是论文直接声明的。

---

## 层面 2：**“都会变成四项”** 这件事没有普遍性

这个就**没有**。

Example 1 之所以变成四项，只是因为这个具体公式

$
(p;q)\ prj\ r
$

在正规化以后恰好有四个分支。\
换别的公式，可能是：

- 1 项
- 2 项
- 6 项
- 更多项

所以普遍的不是“结果长成四项”，而是“都能长成 NF 结构”。

---

# 九、论文为什么要放这个例子

这个例子的真正作用不是让你去记这四项，而是证明一件事：

> 即使是含有顺序算子 `;` 和投影算子 `prj` 的复杂 PPTL 公式，也能被改写成标准 NF。fileciteturn7file6

这样到了第 3 节，作者就可以说：

因为每个 PPTL 公式都能转成 NF，所以 bounded semantics 里不必逐个处理所有复杂算子，只需处理 $\vee,\neg,\circ$ 以及 $\varepsilon,\epsilon'$ 这些基本形式。论文后面确实就是这么说的。fileciteturn7file6

这就是 2.3 和 3.1 能接上的关键。

---

# 十、你现在最该抓住的理解

你不要把 Example 1 理解成“神秘计算题”，而应该理解成：

### 它是在做“结构展开”

不是数值计算，不是概率计算，也不是代数恒等变形那么简单。

### 它的目标是把复杂公式变成统一模板

模板就是：

- 当前结束
- 或者当前满足条件，下一步继续

### 这种方法对所有 PPTL 公式都适用

这是 Theorem 1 保证的。fileciteturn7file6

---

# 十一、如果严格追问“每一步到底怎么推出来”

那我得很诚实地说：

- **这篇论文正文没有给出 Example 1 的完整逐步推导**
- 它只给了结果，并把一般性证明指向文献 \[26]。fileciteturn7file6

所以如果你想要“从 $(p;q)\ prj\ r$ 到那四项的每一步机械推导规则”，严格来说需要去看它引用的 \[26]，也就是 PPTL 逻辑本体那篇文献里的正规化规则。

但基于这篇论文本身，我们已经可以确定两件事：

1. 这四项来自 **projection + sequence 的语义展开**
2. 这种正规化具有**一般性**，不是这个例子特有。fileciteturn7file7turn7file6

---

# 十二、一句话回答你的问题

**Example 1 之所以算成那四项，是因为作者把 $(p;q)\ prj\ r$ 按 PPTL 的顺序语义、投影语义和正规型模板，展开成了“当前结束”或“当前继续”的全部局部分支；这种“化成 NF”的思想具有普遍性，因为论文定理 1 明确说明任意 PPTL 公式都可以改写成正规型，但“恰好四项”只是这个具体公式的结果，不具有普遍性。** fileciteturn7file6turn7file7

下一步最合适的是，我直接给你做一版 **“把 Example 1 的四项按分段语义手工演示”**，用状态序列画出来，你会一下子看懂。


#### You:
这里的p，q指的是状态吗

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
这里的 **$p,q$** 严格说**不是“状态”本身**，而是 **原子命题（atomic propositions）**，也就是在状态上取真或假的命题。论文在 2.1 里先定义 $p\in Prop$，而在 2.2 里又说一个状态 $s_i$ 是从 `Prop` 到布尔值集合 $B=\{\top,\bot\}$ 的映射。fileciteturn7file7

所以关系是这样的：

- **状态 $s\_i$**：一个“赋值点”
- **原子命题 $p,q,r$**：在这个状态上可以判断真假的性质
- **真假关系**：比如 $s_i[p]=\top$ 表示“在状态 $s_i$ 下，命题 $p$ 为真”fileciteturn7file7

---

## 直观地说

你可以把“状态”理解成一个时刻系统的完整快照，比如：

- 进程是否在运行
- 资源是否空闲
- 请求是否到达
- 任务是否完成

而 $p,q$ 只是从这个完整快照里抽出来看的某个性质，例如：

- $p$：CPU 空闲
- $q$：任务已完成
- $r$：调度条件满足

所以：

> **状态是整体，$p,q$ 是贴在状态上的标签/性质。**

---

## 为什么你会觉得它像“状态”

因为在正规型里经常出现：

$
p \land q \land r \land \varepsilon
$

这种写法看起来像“当前这个状态就是 $p,q,r$”。  
但更准确地说，它的意思是：

> **当前状态同时满足命题 $p,q,r$**，并且当前已经到区间末尾。

不是说 $p$ 或 $q$ 本身就是状态。

---

## 在 Example 1 里怎么理解

例如这一项：

$
r\land q\land p\land \varepsilon
$

意思不是“当前有三个状态 $r,q,p$”，而是：

- 当前状态满足 $r$
- 当前状态满足 $q$
- 当前状态满足 $p$
- 并且当前是最后一个位置

也就是：

> **同一个当前状态上，三个原子命题都为真。**

---

## 用论文语义直接说

论文给原子命题的语义是：

$
(\sigma,k,j)\models p \iff s_k[p]=\top
$

这句话已经直接说明了：

- $p$ 是命题
- $s_k$ 是状态

- “$p$ 成立”是指 $p$ 在状态 $s_k$ 上取真fileciteturn7file7

---

## 一句话总结

**$p,q$ 不是状态，而是原子命题；状态是对这些原子命题进行真假赋值的对象。说“$p$ 成立”，本质上就是“当前状态满足命题 $p$”。**

下一步你这里最容易混淆的，其实是“**状态公式**”和“**时序公式**”的区别。


#### You:
![image](sediment://file_000000009c2471fdb57a3395ef40e78c)
那p;q如何用这个图片的理解方式得出呢

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
可以，**就按你图里那种“先抓最外层算子，再看语义”的方式**来理解 $p;q$。

关键先抓住这条定义：

$
P;Q \overset{def}= (P,Q)\ prj\ \varepsilon
$

所以

$
p;q \equiv (p,q)\ prj\ \varepsilon
$

这是论文表 1 直接给的定义。fileciteturn8file1

---

## 1. 先照着你图里的套路看最外层

你图里对 $(\cdots)\ prj\ r$ 的理解是：

- 前面各段满足对应公式
- 投影区间满足后面的公式

现在对 $p;q$ 也一样，因为它本质上就是：

$
(p,q)\ prj\ \varepsilon
$

所以这里：

- 前面的两段分别满足 $p$ 和 $q$
- 后面的 $\varepsilon$ 约束投影区间

根据 projection 的语义，
$
\mathcal I \models (P_1,\dots,P_m)\ prj\ Q
$
当且仅当存在分段点 $r_0,\dots,r_m$，使每段分别满足 $P_1,\dots,P_m$，并且投影区间 $\sigma_q$ 满足 $Q$。fileciteturn8file2turn8file7

---

## 2. 这里的 $\varepsilon$ 到底在要求什么

这里最关键。

因为 $p;q$ 里后面的不是 $r$，而是 **$\varepsilon$**。  
而论文里 $\varepsilon$ 定义为：

$
\varepsilon \overset{def}= \neg \circ \top
$

意思是：

> **当前已经是最后一个状态。**

这是表 1 的 A1。fileciteturn8file1turn8file6

所以：

$
p;q \equiv (p,q)\ prj\ \varepsilon
$

就不是“投影区间当前第一个状态满足某个原子命题”，而是：

> **投影出来的新区间，必须在当前就结束。**

也就是：

> 分成一段 $p$、一段 $q$ 之后，投影区间不能再往后拖，必须正好在这里收住。

---

## 3. 用你图里的同一句话模板来翻译

你图里那句模板是：

> 只要要求投影区间满足 $r$，本质上就是要求投影区间的当前第一个状态满足 $r$。

那么对 $p;q$ 来说，对应要改成：

> 只要要求投影区间满足 $\varepsilon$，本质上就是要求**投影区间当前就是最后一个状态**。

这就是 `;` 的核心含义。

---

## 4. 所以为什么 $p;q$ 叫“先 p 再 q”

因为它要求存在分段点，使得：

- 第一段满足 $p$
- 第二段满足 $q$
- 然后投影出来以后，整个过程**就在这里结束**

所以它表达的是一种**顺序拼接**：

> 先完成 $p$，再完成 $q$，而且这两段合起来正好构成当前整个区间。

这就是为什么 `;` 被叫做“顺序算子”。

---

## 5. 你可以和 $(\cdots)\ prj\ r$ 对比着记

### 情况 A：$(P,Q)\ prj\ r$
后面是原子命题 $r$，所以重点是：

> 投影区间的当前起点满足 $r$

### 情况 B：$(P,Q)\ prj\ \varepsilon$
后面是 $\varepsilon$，所以重点是：

> 投影区间当前就结束

所以：

- 后面是 **原子命题**，你就看“投影区间当前状态满足什么”
- 后面是 **$\varepsilon$**，你就看“投影区间是不是已经结束”

---

## 6. 为什么 Example 1 里会同时出现 $p,q$ 和 $\varepsilon$

Example 1 里有一项：

$
r\land q\land p\land \varepsilon
$

你现在就可以分两层看：

### 最外层 $(p;q)\ prj\ r$
要求投影区间当前起点满足 $r$，所以会带出 $r$。fileciteturn8file7turn8file5

### 里层 $p;q$
而 $p;q=(p,q)\ prj\varepsilon$，表示：

- 前两段分别满足 $p,q$
- 并且投影区间当前就结束

所以在“立刻结束”的那个分支里，就会把 $p,q,\varepsilon$ 一起带出来。

---

## 7. 最直观的小例子

假设当前区间只有一个状态 $s_k$。

如果这个状态同时满足 $p$ 和 $q$，而且当前就是最后一个状态，那么：

- 第一段可以退化在这个点上满足 $p$
- 第二段也可以退化在这个点上满足 $q$
- 投影区间也就在这个点结束，于是满足 $\varepsilon$

所以这种极端情况下，$p;q$ 可以在当前点直接成立，于是就会出现类似

$
p\land q\land \varepsilon
$

这种“结束项”。

这也解释了为什么 Example 1 的第一项是

$
r\land q\land p\land \varepsilon
$

---

## 8. 一句话总结

**按你图里的理解方式，$p;q$ 就看成 $(p,q)\ prj\varepsilon$：前两段分别满足 $p$ 和 $q$，而后面的 $\varepsilon$ 不再要求“投影区间起点满足某命题”，而是要求“投影区间当前就结束”，所以 `;` 的含义就是“先 $p$ 后 $q$，并且这一顺序组合正好在这里收尾”。** fileciteturn8file1turn8file7

下一步最适合的是我直接给你画一个 **3 个状态的具体分段图**，把 $p;q$ 和 $(p;q)\ prj\ r$ 连在一起手工演示。


#### You:
 转换成范式的计算过程这个太难理解，是如何把(p;q) prj r代换到 含Q的范式中的

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
对，这里你卡住的点其实是：

> **“怎么把 $(p;q)\ prj\ r$ 代进含 $Q$ 的范式公式里？”**

真正答案是：

> **不是把 $(p;q)\ prj\ r$ 机械地‘代入’**
> $
> NF(Q)\equiv Q\_e\land \varepsilon \vee \bigvee\_i(Q\_i\land \circ Q\_i')
> $
> 这个式子里，
> 而是把 $Q$ 当成一个**任意公式的占位符**，然后对具体公式
> $
> Q=f=(p;q)\ prj\ r
> $
> 做**等价改写**，最后把它改写成“结束项 + 继续项”的结构。fileciteturn9file1turn9file8

也就是说，2.3 里的 $Q$ 不是一个真的算子，不是让你做普通代数里的“直接代入”。\
它只是说：

> 任意公式 $Q$，都能被改写成那种 NF 形状。fileciteturn9file1turn9file8

---

# 一、先把你这个误区纠正掉

定义 1：

$
NF(Q)\equiv \bigvee_{j=1}^{n_0}(Q_{e_j}\land \varepsilon)\vee \bigvee_{i=1}^{n}(Q_{c_i}\land \circ Q_i')
$

它表达的不是：

> “把一个公式直接塞进去，立刻按模板替换出结果”。

而是：

> “对于任意给定的 PPTL 公式 $Q$，存在一些状态公式 $Q_e,Q_i$ 和一些后继公式 $Q_i'$，使得这个 $Q$ 与右边那种形式等价。”fileciteturn9file1turn9file8

所以这里是**存在性定义**，不是普通的函数代值。

---

# 二、那 $(p;q)\ prj\ r$ 到底怎么和 $Q$ 对应

这里非常简单：

- 在定义里，$Q$ 是任意公式
- 在 Example 1 里，作者取
  $
  f \equiv (p;q)\ prj\ r
  $
- 然后去求
  $
  NF(f)
  $

也就是把“任意公式 $Q$”这件事，具体化成了这个特殊公式 $f$。论文原文就是这样写的：先给出 NF 定义和“任意 PPTL 公式都可改写成 NF”的定理，再给 Example 1：  
$
f\equiv (p;q)\ prj\ r,\quad \text{we can get }NF(f)\equiv \cdots
$
fileciteturn9file1turn9file8

所以严格说，不是“代到含 $Q$ 的范式里”，而是：

> **令 $Q=f=(p;q)\ prj\ r$，然后去求这个具体公式的 NF。**

---

# 三、真正要做的不是“代入”，而是“拆成两类情形”

正规型的目标结构只有两类：

## 第一类：结束项
$
Q_e\land \varepsilon
$

意思是：

- 当前满足某个状态条件
- 并且当前已经结束

## 第二类：继续项
$
Q_i\land \circ Q_i'
$

意思是：

- 当前满足某个状态条件
- 下一步开始满足剩余公式 $Q_i'$

所以对任何具体公式 $f$，你都要问：

> 从当前状态看，$f$ 成立时，
> 是不是有一些情形会“现在就结束”？
> 其余情形是不是都能写成“当前满足某条件，下一步继续检查某个剩余公式”？

这就是 NF 的本质。fileciteturn9file1turn9file8

---

# 四、对 $f=(p;q)\ prj\ r$，先把里面的 `;` 展开

论文表 1 给出：

$
P;Q \overset{def}= (P,Q)\ prj\ \varepsilon
$

所以：

$
p;q \equiv (p,q)\ prj\ \varepsilon
$

因此

$
f=(p;q)\ prj\ r
$

本质上是

$
((p,q)\ prj\ \varepsilon)\ prj\ r
$

虽然论文 Example 1 没把这一步显式写出来，但这是由表 1 的定义直接得到的。fileciteturn9file4turn9file9

---

# 五、再按最外层 `prj` 的语义去拆

论文给出的 projection 语义是：

$
\mathcal I \models (P_1,\dots,P_m)\ prj\ Q
$

当且仅当存在分段点 $r_0,\dots,r_m$，使得每一段分别满足 $P_1,\dots,P_m$，并且投影区间 $\sigma_q$ 满足 $Q$。fileciteturn9file2turn9file5

所以对

$
(p;q)\ prj\ r
$

来说，你可以按图里的方式先抓住两件事：

### 1. 最外层后件是 $r$
而原子命题语义是：

$
(\sigma,k,j)\models r \iff s_k[r]=\top
$

所以只要最外层要求投影区间满足 $r$，当前起点就必须先满足 $r$。fileciteturn9file2turn9file4

这就是为什么 Example 1 的每一项都带着 $r$。

### 2. 前件是 $p;q$
而 $p;q$ 又要求“先 $p$ 再 $q$，并且这个组合正好结束”。fileciteturn9file4

所以当前起点通常还要带着 $p$，而某些结束情形还会把 $q$ 一起带出来。

---

# 六、为什么 Example 1 的结果符合 NF 结构

论文给出的结果是：

$
NF(f)\equiv (r\land q\land p\land \varepsilon)\vee(r\land p\land \circ(\top;q))
\vee(r\land q\land p\land \circ\top)\vee(r\land p\land \circ(\top;(q;\top)))
$

fileciteturn9file8

你现在不要把它看成“神秘计算结果”，而要看结构。

---

## 第一项
$
r\land q\land p\land \varepsilon
$

这是一个标准的 **结束项**：

- 当前状态条件是 $r\land q\land p$
- 并且当前结束 $\varepsilon$

所以它对应 NF 里的

$
Q_e\land \varepsilon
$

---

## 后三项
$
(r\land p\land \circ(\top;q))
\vee(r\land q\land p\land \circ\top)
\vee(r\land p\land \circ(\top;(q;\top)))
$

这些都是标准的 **继续项**：

- 当前状态条件分别是
  - $r\land p$
  - $r\land q\land p$
  - $r\land p$
- 下一步的剩余公式分别是
  - $\top;q$
  - $\top$
  - $\top;(q;\top)$

所以它们都对应 NF 里的

$
Q_i\land \circ Q_i'
$

---

# 七、所以“代换到含 $Q$ 的范式”到底是怎么做的

最准确的说法是：

### 第一步
把
$
f=(p;q)\ prj\ r
$
当作“那个任意公式 $Q$”。

### 第二步
根据 `;` 和 `prj` 的语义，分析它在当前状态成立时有哪些可能的局部形态。  
也就是：

- 哪些情形是“当前就结束”
- 哪些情形是“当前满足什么，下一步再继续”

### 第三步
把这些情形整理成统一形式：
$
Q_e\land \varepsilon \vee \bigvee_i(Q_i\land \circ Q_i')
$

### 第四步
对这个具体公式 $f$，整理后恰好得到 1 个结束项 + 3 个继续项，也就是 Example 1 那四项。fileciteturn9file1turn9file8

---

# 八、你可以把它类比成“模式匹配”，不是“代数代入”

你之所以觉得难，是因为你把

$
NF(Q)\equiv Q_e\land \varepsilon \vee \bigvee_i(Q_i\land \circ Q_i')
$

看成了类似

$
f(x)=x^2+1,\ \text{把 }x=3\text{ 代进去}
$

这种函数代入。

但这里不是。

这里更像是：

> 给你一个复杂公式 $f$，  
> 你要把它**改写成某种目标模板**；
> 这个模板规定：所有结果都必须长成  
> “结束项 or 继续项”。

所以这是**结构归约**，不是普通代值。

---

# 九、为什么作者没写出一步步的“计算规则”

这也是你难受的根本原因之一。

论文在 2.3 里只给了：

- NF 的定义
- Theorem 1：任意 PPTL 公式都能改写成 NF
- Example 1 的结果

但**没有把 Example 1 的每一步正规化规则都写出来**，而是说证明见文献 [26]。fileciteturn9file1turn9file8

所以你现在觉得“怎么突然就变成四项了”，这是正常的。  
因为论文正文确实省略了中间推导。

---

# 十、你现在最该这样理解

把 Example 1 理解成下面这句话就对了：

> 公式
> $
> (p;q)\ prj\ r
> $
> 经过语义展开后，可以分成若干种局部情况；  
> 其中一类是“当前就结束”，另外几类是“当前满足某些状态条件，下一步继续完成剩余结构”；  
> 所以它最终能写成 NF 要求的标准形。fileciteturn9file8turn9file2

---

# 十一、最简短地回答你的问题

**不是把 $(p;q)\ prj\ r$ 直接“代换进” $NF(Q)$ 这个式子里，而是把它看成一个具体的 $Q$，然后依据 `;` 和 `prj` 的语义，把它等价改写成 NF 规定的“状态条件 ∧ 结束”或“状态条件 ∧ 下一步剩余公式”的形式。**

---

下一步最有效的办法，是我直接给你写一版 **“半形式化推导链”**，从  
$
f=(p;q)\ prj\ r
$
出发，不追求严格公理化证明，但一步一步解释为什么会分裂出那 4 项。


#### You:
这些继续项和状态公式是如何得出的

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
是这样得出的，但我先说清一个关键事实：

**这篇论文没有把 Example 1 的中间推导规则逐步写出来。**\
它只给了 NF 的定义、定理“任意 PPTL 公式都能化成 NF”，然后直接给出
$
f\equiv (p;q)\ prj\ r
$
的结果。论文明确说正规型定理的证明见文献 [26]，不是在本文正文里展开。fileciteturn10file1

所以你现在问“这些继续项和状态公式如何得出”，最准确的回答是：

> **正文没有给出机械推导算法；但可以根据 NF 的结构要求和 $;$、$prj$、原子命题、$\circ$ 的语义，反向理解这些项为什么必须长成这样。** fileciteturn10file1turn10file5

下面我就按这个方式讲。

---

## 1. 先看 NF 对“继续项”和“状态公式”有什么硬要求

正规型定义是：

$
NF(Q)\equiv Q_e\land \varepsilon \ \vee\ \bigvee_i (Q_i\land \circ Q_i')
$

而且作者特别强调：  
**$Q_e$ 和 $Q_i$ 都必须是 state formulas（状态公式）**。fileciteturn10file1

这句话决定了两件事：

### 第一，什么叫“状态公式”
就是**不带时序算子**的公式，只说“当前状态满足什么”。

所以像这些才可以放在 $Q_i$ 的位置：

- $r\land p$
- $r\land q\land p$

因为它们都只是原子命题的合取，没有 `○`、`prj`、`;` 之类时序结构。

---

### 第二，什么叫“继续项”
继续项必须长成：

$
Q_i\land \circ Q_i'
$

意思是：

- 当前状态先满足一个纯状态条件 $Q_i$
- 然后“下一步”开始，剩下的任务交给 $Q_i'$

所以所谓“继续项是怎么得出的”，本质上就是：

> **先抽取当前这一步必须立即满足的原子命题条件，作为状态公式 $Q_i$；再把还没完成的时序部分塞进 $\circ Q_i'$ 里。**

---

## 2. Example 1 里的结果先拆开看

论文给的是：

$
NF(f)\equiv (r\land q\land p\land \varepsilon)\vee(r\land p\land \circ(\top;q))
\vee(r\land q\land p\land \circ\top)\vee(r\land p\land \circ(\top;(q;\top)))
$

其中：

- 第一项是**结束项**
- 后三项是**继续项** fileciteturn10file2

我们只看后三项：

$
(r\land p)\land \circ(\top;q)
$
$
(r\land q\land p)\land \circ\top
$
$
(r\land p)\land \circ(\top;(q;\top))
$

于是你马上能看出来：

### 这里的状态公式是
- $Q_1 = r\land p$
- $Q_2 = r\land q\land p$
- $Q_3 = r\land p$

### 这里的继续部分是
- $Q_1' = \top;q$
- $Q_2' = \top$
- $Q_3' = \top;(q;\top)$

也就是说，**状态公式**就是每个继续项里 `○` 前面的那一坨；  
**继续项**就是这整个 $Q_i\land \circ Q_i'$ 结构。fileciteturn10file1turn10file2

---

## 3. 为什么状态公式里会出现 $r$

因为最外层是：

$
(p;q)\ prj\ r
$

而 projection 语义说：

$
\mathcal I \models (P_1,\dots,P_m)\ prj\ Q
$

当且仅当存在分段点，使前面的各段满足 $P_1,\dots,P_m$，并且投影区间 $\sigma_q$ 满足 $Q$。fileciteturn10file5

现在这里的 $Q$ 就是原子命题 $r$。  
原子命题语义是：

$
(\sigma,k,j)\models r \iff s_k[r]=\top
$

也就是：**当前第一个状态必须满足 $r$**。fileciteturn10file5

所以不管是哪一种分支，只要最外层还要求 `prj r`，当前状态条件里通常都要把 $r$ 带上。  
这就是为什么三个继续项里都有 $r$。

---

## 4. 为什么状态公式里会出现 $p$

因为里面有 $p;q$，而表 1 定义：

$
P;Q \overset{def}= (P,Q)\ prj\ \epsilon
$

所以

$
p;q \equiv (p,q)\ prj\ \epsilon
$

这表示：前一段满足 $p$，后一段满足 $q$，并且这个顺序组合正好结束。fileciteturn10file5

由于第一段是从当前起点开始的，所以要让这个顺序结构成立，**当前起点先满足 $p$** 是最自然、也是必须抽出的“当前条件”之一。  
所以继续项里的状态公式通常会带 $p$。

---

## 5. 为什么有的继续项里还带 $q$，有的不带

这是最关键的地方。

它反映的是：

> 在不同的局部分支里，**$q$ 是“当前这一步已经完成了”，还是“留到后面再完成”**。

---

### 分支 A
$
(r\land p)\land \circ(\top;q)
$

这里状态公式里**没有 $q$**，说明：

- 当前这一步只强制要求 $r$ 和 $p$
- $q$ 还没要求现在就真
- 它被放到后面的剩余公式 $\top;q$ 里了

也就是：

> 当前只开了个头，后面再去完成 $q$。

---

### 分支 B
$
(r\land q\land p)\land \circ\top
$

这里状态公式里**有 $q$**，而剩余部分只剩 $\top$。  
这说明：

- 当前这一步已经把 $r,p,q$ 都凑齐了
- 后面不再有实质要求，所以只剩最弱公式 $\top$

也就是：

> 关键要求已经在当前点完成，后面随便走。

---

### 分支 C
$
(r\land p)\land \circ(\top;(q;\top))
$

这里当前仍然**不要求 $q$**，因为 $q$ 被留在更长的未来结构里了：

$
\top;(q;\top)
$

说明这是另一种“更晚才完成 $q$”的局部形态。

---

## 6. 所以“状态公式”到底怎么抽出来

你可以记一个非常实用的规则：

> **把一个具体 PPTL 公式改写成 NF 时，先看“当前状态必须立刻成立哪些原子命题或布尔条件”，把这些抽成状态公式；再把所有还没完成的时序任务，统一塞到 $\circ(\cdots)$ 后面。**

套到 Example 1：

### 当前立刻必须满足的
- 最外层 `prj r` 带来 $r$
- 内层顺序结构开头带来 $p$
- 某些分支里 $q$ 也已经在当前点完成，所以再加上 $q$

于是就得到状态公式：

- $r\land p$
- 或 $r\land q\land p$

### 还没完成的未来任务
根据不同分支，未来剩余结构不同，于是得到：

- $\top;q$
- $\top$
- $\top;(q;\top)$

这就是继续项的来源。

---

## 7. 为什么继续部分前面一定有 `○`

因为 NF 的第二类项定义死了就是：

$
Q_i\land \circ Q_i'
$

而 `○` 的语义是：

$
(\sigma,k,j)\models \circ P \iff k<j \text{ and } (\sigma,k+1,j)\models P
$

意思是：

> 剩余任务从“下一状态”开始检查。fileciteturn10file5

所以只要当前还没结束，NF 就会把未来任务放到 `○` 后面。  
这就是为什么继续项统一长成那样。

---

## 8. 你可以把它理解成“当前义务 + 剩余义务”

这是最好记的版本。

对于每个继续项：

$
Q_i\land \circ Q_i'
$

- **$Q_i$**：当前义务，必须现在就满足，所以必须是状态公式
- **$Q_i'$**：剩余义务，留到下一步继续满足，所以放到 `○` 后面

以 Example 1 为例：

### 项 1
$
(r\land p)\land \circ(\top;q)
$
当前义务：$r\land p$  
剩余义务：$\top;q$

### 项 2
$
(r\land q\land p)\land \circ\top
$
当前义务：$r\land q\land p$  
剩余义务：$\top$

### 项 3
$
(r\land p)\land \circ(\top;(q;\top))
$
当前义务：$r\land p$\
剩余义务：$\top;(q;\top)$

---

## 9. 这里有没有一套论文正文里明确写出的“计算步骤”？

**没有。**

这是最需要诚实说明的地方。\
本文只给了：

- NF 的目标形式
- “任意 PPTL 公式都能改写成 NF”的定理
- Example 1 的结果

但没有给出“先用规则 A，再用规则 B，再用规则 C”的详细正规化过程。作者明确把定理证明指向文献 \[26]。fileciteturn10file1

所以如果你在追求：

> “为什么正好是这 3 个继续项，而不是别的 3 个？”

那严格的机械推导要去看它引用的 \[26]。\
就这篇论文正文本身，我们只能做到**基于语义的结构解释**，不能伪装成已经看到了完整推导表。

---

## 10. 最后压缩成一句话

**这些状态公式，是从该分支下“当前状态必须立即满足的条件”里抽出来的，因此必须是不含时序算子的布尔条件；这些继续项，则是把“当前义务”写成 $Q_i$，把“尚未完成的未来时序任务”写成 $Q_i'$，统一整理成 $Q_i\land \circ Q_i'$ 的 NF 结构。Example 1 中的 $r\land p$、$r\land q\land p$ 就是这样来的，而 $\top;q$、$\top$、$\top;(q;\top)$ 则分别对应不同分支下剩余的未来任务。** fileciteturn10file1turn10file2turn10file5

下一步我建议直接做一件最有帮助的事：我给你画成“树状分裂图”，从 $(p;q)\ prj\ r$ 开始，一层层分出“当前必须满足什么”和“下一步剩下什么”。


#### You:
当前状态满足r，这个状态是r后续状态的开始对吗，那是(p,q)这个投影区间的结束吗？

#### ChatGPT:
\[Unsupported Content]


#### Plugin (file_search):
Make sure to include fileciteturn12file0 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 , 𝑠𝑡1 ,… , 𝑠𝑡𝑛 ⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ … 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁 , and 𝑡0, 𝑡1,… , 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,… , 𝑟𝑚 by deleting 
all duplicates. That is, 𝑡0,… , 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,… , 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case, 
𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1,𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected 
intervals are given below (See Fig. 1).

(a) ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,3,4,4,4,6) = ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,4,6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0,0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47,47,𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47) = ⟨𝑠0, 𝑠21, 𝑠47⟩

Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1 ,… , 𝑃𝑚 are interpreted 
in the projection construct. In order to interpret the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞

as follows:

Let 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠𝑚,… , 𝑠𝑗⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is 
interpreted over a subinterval 𝜎(𝑟𝑖−1 ..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,… , 𝑠𝑟𝑖⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in 
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination 
of 𝑃𝑚 (see red color sequence).

Thus, we define 𝜎𝑞 as follows:

𝜎(𝑟𝑚+1..𝑗) =

{
< 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,

ε, if 𝑟𝑚 = 𝑗.

𝜎𝑞 = 𝜎 ↓ (𝑟0,… , 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)



Theoretical Computer Science 1049 (2025) 115368

4

Z. Duan, C. Tian, N. Zhang et al. 

Table 1
Derived formulas.

A1 𝜀
def
= ¬○⊤ A2 𝜖def= ○⊤

A3 ⨀
𝑃

def
= 𝜀 ∨○𝑃 A4 𝑃 ;𝑄

def
= (𝑃 ,𝑄) 𝑝𝑟𝑗 𝜀

A5 ◊ 𝑃
def
= ⊤;𝑃 A6 □𝑃

def
= ¬◊¬𝑃

A7 𝑓𝑖𝑛
def
= ◊𝜀 A8 𝑖𝑛𝑓

def
= ¬𝑓𝑖𝑛

A9

{
○0𝑃

def
= 𝑃

○𝑛𝑃
def
= ○(○𝑛−1𝑃 )(𝑛 > 0)

A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧𝑄 ∨ 𝑃 ∧ (𝑄;⊤)

∨𝑃 ∧𝑄 ∧□

𝜖

A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)

𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.

PPTL formulas are interpreted over intervals. An interpretation  = (𝜎,𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,… , 𝑠𝑗⟩ of 𝜎 with the current state 
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎 ⊧ 𝑃

if 𝜎(0, |𝜎|) ⊧ 𝑃 .

(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.

(2)  ⊧○𝑃 iff 𝑘 < 𝑗 and (𝜎,𝑘+ 1, 𝑗) ⊧ 𝑃 .

(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .

(4)  ⊧ 𝑃 ∨𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.

(5)  ⊧ (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎, 𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all 
1 ≤ 𝑙 ≤𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞,0, |𝜎𝑞|) ⊧ 𝑄).

Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎 ⊧ 𝑝, if (𝜎,0, |𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable 
if 𝜎 ⊧ 𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎 ⊧ 𝑝 for all 𝜎.

Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤
def
= 𝑃 ∨ ¬𝑃 and ⊥

def
= 𝑃 ∧ ¬𝑃 , for any 

formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.

2.3. Normal form

Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL 
formula 𝑄. Then, the NF can be defined as follows:

Definition 1. Normal Form of 𝑄:

𝑁𝐹 (𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) ∨ ∨𝑛

𝑖=1(𝑄𝑐𝑖 ∧○𝑄′
𝑖
)

To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟

𝑖=1(𝑄𝑖 ∧○𝑄′
𝑖
) to replace 

∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧○𝑄′

𝑖
). Thus,

𝑁𝐹 (𝑄) ≡𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧○𝑄′

𝑖
)

where 𝑄𝑒 and 𝑄𝑖 are state formulas.

Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.

The proof of this theorem can be found in [26].

Example 1. Given a PPTL formula 𝑓 , 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get

𝑁𝐹 (𝑓 ) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧○⊤) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; (𝑞;⊤)))

3. Principle of SAT-based bounded model checking with PPTL

In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we 
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of 
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and 
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only 
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖

. In the following, we define the bounded semantics of PPTL formulas. 
Let 𝜎 be an interval and 𝑃 a PPTL formula.



Theoretical Computer Science 1049 (2025) 115368

5

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 3. 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝. 

3.1. Bounded semantics

In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.

Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼, 𝑇 ,𝐿) where 𝑆 is the set of sates, 𝐼 ⊆ 𝑆 is the set of initial states, 
𝑇 ⊆ 𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.

We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can 
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite. 
Therefore, in the following, we give the definition of 𝑘− 𝑙𝑜𝑜𝑝 in an interval.

Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,… , 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,… , 𝑠𝑘⟩𝜔, we call 
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.

Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈𝑁0. Now we can define the successor of state 
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:

𝑠𝑢𝑐𝑐(𝑖) =
⎧⎪⎨⎪⎩

𝑖+ 1 if 𝑖 < 𝑘

𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝

𝑘+ 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval 

With bounded model checking of PPTL, given a bound 𝑘 ∈𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an 
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval 
< 𝑠𝑖,… , 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to 
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .

The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition

(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘

(𝜎, 𝑖) ⊧𝑘

𝜖

iff 𝑖 < 𝑘

A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎,0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have 
𝜎 ⊧𝑘 𝑃 iff (𝜎,0, 𝑘) ⊧ 𝑃 .

As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics 
of PPTL is sound.

3.2. Bounded model checking

According to the structure of interval 𝜎, two basic lemmas are given below:

Lemma 1. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓 .

Proof. To prove Lemma 1, we first prove a stronger conclusion given below:

(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)

Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓 :

Base case:

𝑓 ≡ 𝑝 ∈ 𝑃𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖, |𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑝.



Theoretical Computer Science 1049 (2025) 115368

6

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 4. 𝜎 is a finite interval. 

Inductive cases:

1. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Then, we have, (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 . Further, 
(𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 and (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 , leading to (𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 .

2. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Since 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝, so, 𝑠𝑢𝑐𝑐(𝑖) ≤ 𝑘 < |𝜎|. Then, by 
hypothesis, we have,

(𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 . By the definitions of semantics, (𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 ○𝑓

iff (𝜎, 𝑖, 𝑘) ⊧○𝑓 and (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖+ 1, |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 , so (𝜎, 𝑖, 𝑘) ⊧○𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 .

3. Suppose for any PPTL formulas 𝑓1 and 𝑓2, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 and (𝜎, 𝑖, 𝑘) ⊧ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓2. Then, by the 
definitions of bounded semantics and model semantics, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 ∨ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 ∨ 𝑓2. □

Note that we do not need to deal with 𝜀 and 𝜖

in the above inductive cases since 𝜀 ≡ ¬○⊤ and 𝜖

≡○⊤.

Lemma 2. Let f be a PPTL formula, and 𝜎 a finite interval (Fig. 4). Then 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 .

Proof. Since 𝜎 is a finite interval, so |𝜎| ∈𝑁0.

𝜎 ⊧ 𝑓 ⇔ (𝜎,0, |𝜎|) ⊧ 𝑓

⇔ (𝜎,0, 𝑘) ⊧ 𝑓 ∧ 𝑘 = |𝜎|
⇒ ∃𝑘,𝑘 ≥ 0, (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 □

Theorem 2. Suppose a system is described by a Kripke structure M, and some property is defined by a PPTL formula 𝑓 . Let 𝑀 be the set 
of all intervals generated in M. We define 𝑀 ⊧ ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 as well as 𝑀 ⊧𝑘 ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . Then we have 
𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 .

Proof. We need prove that ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 iff ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . To do so, we consider intervals in 𝑀 as infinite or finite ones 
respectively.

1. Suppose 𝜎 is infinite, there must be an integer 𝑘 ≥ 0 that makes 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝. By Lemma 1:

𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓

we have,

𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓

2. Suppose interval 𝜎 is finite, i.e., |𝜎| =𝑚 ∈𝑁0.

“ ⇒ ” ∶𝑀 ⊧ ∃𝑓 ⇔ ∃𝜎 ∈𝑀 ∧ 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,Σ ⊧𝑘 ∃𝑓 (Lemma 2)

“ ⇐ ” ∶ ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0, 𝑘) ⊧ 𝑓

Let 𝜎′ =< 𝑠0, 𝑠1,… , 𝑠𝑘 >, we have (𝜎′,0, 𝑘) ⊧ 𝑓 . Since 𝜎′ is a subinterval 

of 𝜎 and |𝜎′| = 𝑘, hence, ∃𝜎′ ∈𝑀 and 𝜎′ ⊧ 𝑓 , leading to 𝑀 ⊧ ∃𝑓.

As a result, ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇒𝑀 ⊧ ∃𝑓. □

3.3. Reducing bounded model checking with PPTL to SAT

Given a finite state transition system 𝑀 (a Kripke structure or NFG), the property of the system in terms of a PPTL formula 𝑓 , and 
a bound 𝑘, then the procedure of BMC can be described as a process for constructing a proposition formula [𝑀,𝑓 ]𝑘. Let ⟨𝑠0,… , 𝑠𝑘⟩ be 
a subinterval of interval 𝜎. The definition of formula [𝑀,𝑓 ]𝑘 consists of two components: 𝑀𝑘, the first component, is a propositional 
formula that constrains ⟨𝑠0,… , 𝑠𝑘⟩ to be a valid interval starting from an initial state; 𝑋𝑘 , the second component, a propositional 



Theoretical Computer Science 1049 (2025) 115368

7

Z. Duan, C. Tian, N. Zhang et al. 

formula that constrains 𝜎 to satisfy 𝑓 with bound 𝑘. To define the second component, we first give the definition of 𝑙𝑜𝑜𝑝 𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛, 
which is a propositional formula that is evaluated to true only if the interval 𝜎 contains a loop; then we give some translation rules 
for formulas.

Definition 4. For a Kripke structure M, and k ≥ 0,

𝑀𝑘

def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1)

Loop condition:

𝐿(𝑘,𝑙)
def 
= 𝑇 (𝑠𝑘, 𝑠𝑙)  (0 ≤ 𝑙 ≤ 𝑘)

𝐿𝑘

def 
= ∨𝑘

𝑙=0 𝐿(𝑘,𝑙)

Let 𝑝 be an atomic proposition, and 𝑓 , 𝑔 be PPTL formulas, 𝜎 an interval with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝, 𝑠𝑖 the current state, and 𝑘 the bound, 
where 0 ≤ 𝑖, 𝑙, 𝑘 ≤ |𝜎|, 𝑖, 𝑙 ≤ 𝑘. The translation of a PPTL formula is given below:

k-loop: Translation 𝑓 (𝑖, 𝑘, 𝑙) of a PPTL formula 𝑓 over an infinite interval 𝜎 with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 is inductively defined as follows.

𝑝(𝑖,𝑘,𝑙)
def 
= 𝑝(𝑠𝑖) if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition, meaning 𝑠𝑖[𝑝]

(¬𝑓 )(𝑖,𝑘,𝑙)
def 
= ¬𝑓(𝑖,𝑘,𝑙)

(𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙)

(○𝑓 )(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑠𝑢𝑐𝑐(𝑖),𝑘,𝑙)

𝜀(𝑖,𝑘,𝑙)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘,𝑙)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

For the translation presented above, a new propositional variable is introduced for each intermediate formula 𝑒(𝑖,𝑘,𝑙), where 𝑒 is a 
sub-formula of PPTL formula 𝑓 and 0 ≤ 𝑖 ≤ 𝑘 and 𝑙 indicates the existence of (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝. If 𝑒 is an atomic proposition or its negation, 
𝑒(𝑖,𝑘,𝑙) is substituted by a boolean variable with the truth-value at state 𝑠𝑖. Otherwise, 𝑒(𝑖,𝑘,𝑙) indicates a propositional formula whose 
satisfiability should be considered over the interval (𝑠𝑖,… , 𝑠𝑘).

no loop: Translation 𝑓 (𝑖, 𝑘) of a PPTL formula 𝑓 for a finite interval 𝜎 (with no loop).

𝑝(𝑖,𝑘)
def 
= 𝑝(𝑠𝑖)

(¬𝑓 )(𝑖,𝑘)
def 
= ¬𝑓(𝑖,𝑘)

(𝑓 ∨ 𝑔)(𝑖,𝑘)
def 
= 𝑓(𝑖,𝑘) ∨ 𝑔(𝑖,𝑘)

(○𝑓 )(𝑖,𝑘)
def 
= 𝑓(𝑖+1,𝑘)

𝑓(𝑘+1,𝑘)
def 
= ⊥

𝜀(𝑖,𝑘)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

When the intermediate formula 𝑒(𝑖,𝑘) appears in a PPTL formula for a finite interval (with no loop), the explanations are similar to 
the ones for a PPTL formula with an interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 and omitted here.

General translation (BMC to SAT): 

𝑋𝑘

def 
= (¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))

[𝑀,𝑓 ]𝑘
def 
= 𝑀𝑘 ∧𝑋𝑘

i.e.:

[𝑀,𝑓 ]𝑘
def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))]



Theoretical Computer Science 1049 (2025) 115368

8

Z. Duan, C. Tian, N. Zhang et al. 

As we can see, the right side of the definition can be divided into two parts: the first part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (¬𝐿𝑘 ∧ 𝑓(0,𝑘))

indicates an interval with no loop and the translation without loop is used; the second part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧
𝑓(0,𝑘,𝑙))) presents that an interval with a 𝑘 − 𝑙𝑜𝑜𝑝 and all possible starting points 𝑙 of a loop and the translation for a 𝑘 − 𝑙𝑜𝑜𝑝 is 
conjoined with the corresponding loop condition 𝐿(𝑘,𝑙).

Lemma 3. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 an interval. The translation 𝑓(𝑖,𝑘,𝑙) or 𝑓(𝑖,𝑘) is defined as above. Then

(1) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘,𝑙) if 𝜎 is infinite with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 or

(2) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘) if 𝜎 is finite.

Proof. We prove only (1) but in a stronger version. A similar proof can be given to prove (2). The proof proceeds by induction on 
the rules of the definition of translation. 
Base: for an atomic proposition 𝑝 ∈ 𝑃𝑟𝑜𝑝.

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ while (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙) iff 𝜎 ⊧𝑘 𝑝(𝑠𝑖) iff 𝑠𝑖[𝑝] = ⊤. So, (𝜎, 𝑖) ⊧𝑘 𝑝 iff (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙)
Induction: 
Suppose (𝜎, 𝑖) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙), (𝜎, 𝑖) ⊧𝑘 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙). We have,

1) (𝜎, 𝑖) ⊧𝑘 ¬𝑓 iff (𝜎, 𝑖) ̸⊧𝑘 𝑓 def

iff (𝜎, 𝑖) ̸⊧𝑘 𝑓(0,𝑘,𝑙) hypothesis 
iff (𝜎, 𝑖) ⊧𝑘 ¬𝑓(0,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (¬𝑓 )(0,𝑘,𝑙) def

2) (𝜎, 𝑖) ⊧𝑘 𝑓 ∨ 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑓 or (𝜎, 𝑖) ⊧𝑘 𝑔 def

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) or (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙) def

3) (𝜎, 𝑖) ⊧𝑘 ○𝑓 iff (𝜎, 𝑖) ⊧○𝑓 Lemma 1
iff (𝜎, 𝑖+ 1) ⊧ 𝑓 Def

iff (𝜎, 𝑖+ 1) ⊧ 𝑓(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧ (○𝑓 )(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (○𝑓 )(𝑖,𝑘,𝑙) Lemma 1

We do not need to consider 𝜀 and 𝜖
again here. When 𝑖 = 0 the Lemma 3 is proved. Now we come to prove an important conclusion 

formalized in Theorem 3.

Theorem 3. [𝑀,𝑓 ]𝑘 is satisfiable iff
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn12file1 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 , 𝑠𝑡1 ,… , 𝑠𝑡𝑛 ⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ … 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁 , and 𝑡0, 𝑡1,… , 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,… , 𝑟𝑚 by deleting 
all duplicates. That is, 𝑡0,… , 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,… , 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case, 
𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1,𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected 
intervals are given below (See Fig. 1).

(a) ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,3,4,4,4,6) = ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,4,6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0,0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47,47,𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47) = ⟨𝑠0, 𝑠21, 𝑠47⟩

Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1 ,… , 𝑃𝑚 are interpreted 
in the projection construct. In order to interpret the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞

as follows:

Let 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠𝑚,… , 𝑠𝑗⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is 
interpreted over a subinterval 𝜎(𝑟𝑖−1 ..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,… , 𝑠𝑟𝑖⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in 
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination 
of 𝑃𝑚 (see red color sequence).

Thus, we define 𝜎𝑞 as follows:

𝜎(𝑟𝑚+1..𝑗) =

{
< 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,

ε, if 𝑟𝑚 = 𝑗.

𝜎𝑞 = 𝜎 ↓ (𝑟0,… , 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)



Theoretical Computer Science 1049 (2025) 115368

4

Z. Duan, C. Tian, N. Zhang et al. 

Table 1
Derived formulas.

A1 𝜀
def
= ¬○⊤ A2 𝜖def= ○⊤

A3 ⨀
𝑃

def
= 𝜀 ∨○𝑃 A4 𝑃 ;𝑄

def
= (𝑃 ,𝑄) 𝑝𝑟𝑗 𝜀

A5 ◊ 𝑃
def
= ⊤;𝑃 A6 □𝑃

def
= ¬◊¬𝑃

A7 𝑓𝑖𝑛
def
= ◊𝜀 A8 𝑖𝑛𝑓

def
= ¬𝑓𝑖𝑛

A9

{
○0𝑃

def
= 𝑃

○𝑛𝑃
def
= ○(○𝑛−1𝑃 )(𝑛 > 0)

A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧𝑄 ∨ 𝑃 ∧ (𝑄;⊤)

∨𝑃 ∧𝑄 ∧□

𝜖

A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)

𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.

PPTL formulas are interpreted over intervals. An interpretation  = (𝜎,𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,… , 𝑠𝑗⟩ of 𝜎 with the current state 
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎 ⊧ 𝑃

if 𝜎(0, |𝜎|) ⊧ 𝑃 .

(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.

(2)  ⊧○𝑃 iff 𝑘 < 𝑗 and (𝜎,𝑘+ 1, 𝑗) ⊧ 𝑃 .

(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .

(4)  ⊧ 𝑃 ∨𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.

(5)  ⊧ (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎, 𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all 
1 ≤ 𝑙 ≤𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞,0, |𝜎𝑞|) ⊧ 𝑄).

Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎 ⊧ 𝑝, if (𝜎,0, |𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable 
if 𝜎 ⊧ 𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎 ⊧ 𝑝 for all 𝜎.

Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤
def
= 𝑃 ∨ ¬𝑃 and ⊥

def
= 𝑃 ∧ ¬𝑃 , for any 

formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.

2.3. Normal form

Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL 
formula 𝑄. Then, the NF can be defined as follows:

Definition 1. Normal Form of 𝑄:

𝑁𝐹 (𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) ∨ ∨𝑛

𝑖=1(𝑄𝑐𝑖 ∧○𝑄′
𝑖
)

To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟

𝑖=1(𝑄𝑖 ∧○𝑄′
𝑖
) to replace 

∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧○𝑄′

𝑖
). Thus,

𝑁𝐹 (𝑄) ≡𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧○𝑄′

𝑖
)

where 𝑄𝑒 and 𝑄𝑖 are state formulas.

Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.

The proof of this theorem can be found in [26].

Example 1. Given a PPTL formula 𝑓 , 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get

𝑁𝐹 (𝑓 ) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧○⊤) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; (𝑞;⊤)))

3. Principle of SAT-based bounded model checking with PPTL

In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we 
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of 
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and 
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only 
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖

. In the following, we define the bounded semantics of PPTL formulas. 
Let 𝜎 be an interval and 𝑃 a PPTL formula.



Theoretical Computer Science 1049 (2025) 115368

5

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 3. 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝. 

3.1. Bounded semantics

In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.

Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼, 𝑇 ,𝐿) where 𝑆 is the set of sates, 𝐼 ⊆ 𝑆 is the set of initial states, 
𝑇 ⊆ 𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.

We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can 
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite. 
Therefore, in the following, we give the definition of 𝑘− 𝑙𝑜𝑜𝑝 in an interval.

Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,… , 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,… , 𝑠𝑘⟩𝜔, we call 
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.

Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈𝑁0. Now we can define the successor of state 
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:

𝑠𝑢𝑐𝑐(𝑖) =
⎧⎪⎨⎪⎩

𝑖+ 1 if 𝑖 < 𝑘

𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝

𝑘+ 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval 

With bounded model checking of PPTL, given a bound 𝑘 ∈𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an 
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval 
< 𝑠𝑖,… , 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to 
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .

The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition

(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘

(𝜎, 𝑖) ⊧𝑘

𝜖

iff 𝑖 < 𝑘

A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎,0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have 
𝜎 ⊧𝑘 𝑃 iff (𝜎,0, 𝑘) ⊧ 𝑃 .

As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics 
of PPTL is sound.

3.2. Bounded model checking

According to the structure of interval 𝜎, two basic lemmas are given below:

Lemma 1. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓 .

Proof. To prove Lemma 1, we first prove a stronger conclusion given below:

(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)

Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓 :

Base case:

𝑓 ≡ 𝑝 ∈ 𝑃𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖, |𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑝.



Theoretical Computer Science 1049 (2025) 115368

6

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 4. 𝜎 is a finite interval. 

Inductive cases:

1. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Then, we have, (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 . Further, 
(𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 and (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 , leading to (𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 .

2. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Since 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝, so, 𝑠𝑢𝑐𝑐(𝑖) ≤ 𝑘 < |𝜎|. Then, by 
hypothesis, we have,

(𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 . By the definitions of semantics, (𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 ○𝑓

iff (𝜎, 𝑖, 𝑘) ⊧○𝑓 and (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖+ 1, |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 , so (𝜎, 𝑖, 𝑘) ⊧○𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 .

3. Suppose for any PPTL formulas 𝑓1 and 𝑓2, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 and (𝜎, 𝑖, 𝑘) ⊧ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓2. Then, by the 
definitions of bounded semantics and model semantics, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 ∨ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 ∨ 𝑓2. □

Note that we do not need to deal with 𝜀 and 𝜖

in the above inductive cases since 𝜀 ≡ ¬○⊤ and 𝜖

≡○⊤.

Lemma 2. Let f be a PPTL formula, and 𝜎 a finite interval (Fig. 4). Then 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 .

Proof. Since 𝜎 is a finite interval, so |𝜎| ∈𝑁0.

𝜎 ⊧ 𝑓 ⇔ (𝜎,0, |𝜎|) ⊧ 𝑓

⇔ (𝜎,0, 𝑘) ⊧ 𝑓 ∧ 𝑘 = |𝜎|
⇒ ∃𝑘,𝑘 ≥ 0, (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 □

Theorem 2. Suppose a system is described by a Kripke structure M, and some property is defined by a PPTL formula 𝑓 . Let 𝑀 be the set 
of all intervals generated in M. We define 𝑀 ⊧ ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 as well as 𝑀 ⊧𝑘 ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . Then we have 
𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 .

Proof. We need prove that ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 iff ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . To do so, we consider intervals in 𝑀 as infinite or finite ones 
respectively.

1. Suppose 𝜎 is infinite, there must be an integer 𝑘 ≥ 0 that makes 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝. By Lemma 1:

𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓

we have,

𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓

2. Suppose interval 𝜎 is finite, i.e., |𝜎| =𝑚 ∈𝑁0.

“ ⇒ ” ∶𝑀 ⊧ ∃𝑓 ⇔ ∃𝜎 ∈𝑀 ∧ 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,Σ ⊧𝑘 ∃𝑓 (Lemma 2)

“ ⇐ ” ∶ ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0, 𝑘) ⊧ 𝑓

Let 𝜎′ =< 𝑠0, 𝑠1,… , 𝑠𝑘 >, we have (𝜎′,0, 𝑘) ⊧ 𝑓 . Since 𝜎′ is a subinterval 

of 𝜎 and |𝜎′| = 𝑘, hence, ∃𝜎′ ∈𝑀 and 𝜎′ ⊧ 𝑓 , leading to 𝑀 ⊧ ∃𝑓.

As a result, ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇒𝑀 ⊧ ∃𝑓. □

3.3. Reducing bounded model checking with PPTL to SAT

Given a finite state transition system 𝑀 (a Kripke structure or NFG), the property of the system in terms of a PPTL formula 𝑓 , and 
a bound 𝑘, then the procedure of BMC can be described as a process for constructing a proposition formula [𝑀,𝑓 ]𝑘. Let ⟨𝑠0,… , 𝑠𝑘⟩ be 
a subinterval of interval 𝜎. The definition of formula [𝑀,𝑓 ]𝑘 consists of two components: 𝑀𝑘, the first component, is a propositional 
formula that constrains ⟨𝑠0,… , 𝑠𝑘⟩ to be a valid interval starting from an initial state; 𝑋𝑘 , the second component, a propositional 



Theoretical Computer Science 1049 (2025) 115368

7

Z. Duan, C. Tian, N. Zhang et al. 

formula that constrains 𝜎 to satisfy 𝑓 with bound 𝑘. To define the second component, we first give the definition of 𝑙𝑜𝑜𝑝 𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛, 
which is a propositional formula that is evaluated to true only if the interval 𝜎 contains a loop; then we give some translation rules 
for formulas.

Definition 4. For a Kripke structure M, and k ≥ 0,

𝑀𝑘

def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1)

Loop condition:

𝐿(𝑘,𝑙)
def 
= 𝑇 (𝑠𝑘, 𝑠𝑙)  (0 ≤ 𝑙 ≤ 𝑘)

𝐿𝑘

def 
= ∨𝑘

𝑙=0 𝐿(𝑘,𝑙)

Let 𝑝 be an atomic proposition, and 𝑓 , 𝑔 be PPTL formulas, 𝜎 an interval with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝, 𝑠𝑖 the current state, and 𝑘 the bound, 
where 0 ≤ 𝑖, 𝑙, 𝑘 ≤ |𝜎|, 𝑖, 𝑙 ≤ 𝑘. The translation of a PPTL formula is given below:

k-loop: Translation 𝑓 (𝑖, 𝑘, 𝑙) of a PPTL formula 𝑓 over an infinite interval 𝜎 with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 is inductively defined as follows.

𝑝(𝑖,𝑘,𝑙)
def 
= 𝑝(𝑠𝑖) if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition, meaning 𝑠𝑖[𝑝]

(¬𝑓 )(𝑖,𝑘,𝑙)
def 
= ¬𝑓(𝑖,𝑘,𝑙)

(𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙)

(○𝑓 )(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑠𝑢𝑐𝑐(𝑖),𝑘,𝑙)

𝜀(𝑖,𝑘,𝑙)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘,𝑙)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

For the translation presented above, a new propositional variable is introduced for each intermediate formula 𝑒(𝑖,𝑘,𝑙), where 𝑒 is a 
sub-formula of PPTL formula 𝑓 and 0 ≤ 𝑖 ≤ 𝑘 and 𝑙 indicates the existence of (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝. If 𝑒 is an atomic proposition or its negation, 
𝑒(𝑖,𝑘,𝑙) is substituted by a boolean variable with the truth-value at state 𝑠𝑖. Otherwise, 𝑒(𝑖,𝑘,𝑙) indicates a propositional formula whose 
satisfiability should be considered over the interval (𝑠𝑖,… , 𝑠𝑘).

no loop: Translation 𝑓 (𝑖, 𝑘) of a PPTL formula 𝑓 for a finite interval 𝜎 (with no loop).

𝑝(𝑖,𝑘)
def 
= 𝑝(𝑠𝑖)

(¬𝑓 )(𝑖,𝑘)
def 
= ¬𝑓(𝑖,𝑘)

(𝑓 ∨ 𝑔)(𝑖,𝑘)
def 
= 𝑓(𝑖,𝑘) ∨ 𝑔(𝑖,𝑘)

(○𝑓 )(𝑖,𝑘)
def 
= 𝑓(𝑖+1,𝑘)

𝑓(𝑘+1,𝑘)
def 
= ⊥

𝜀(𝑖,𝑘)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

When the intermediate formula 𝑒(𝑖,𝑘) appears in a PPTL formula for a finite interval (with no loop), the explanations are similar to 
the ones for a PPTL formula with an interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 and omitted here.

General translation (BMC to SAT): 

𝑋𝑘

def 
= (¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))

[𝑀,𝑓 ]𝑘
def 
= 𝑀𝑘 ∧𝑋𝑘

i.e.:

[𝑀,𝑓 ]𝑘
def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))]



Theoretical Computer Science 1049 (2025) 115368

8

Z. Duan, C. Tian, N. Zhang et al. 

As we can see, the right side of the definition can be divided into two parts: the first part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (¬𝐿𝑘 ∧ 𝑓(0,𝑘))

indicates an interval with no loop and the translation without loop is used; the second part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧
𝑓(0,𝑘,𝑙))) presents that an interval with a 𝑘 − 𝑙𝑜𝑜𝑝 and all possible starting points 𝑙 of a loop and the translation for a 𝑘 − 𝑙𝑜𝑜𝑝 is 
conjoined with the corresponding loop condition 𝐿(𝑘,𝑙).

Lemma 3. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 an interval. The translation 𝑓(𝑖,𝑘,𝑙) or 𝑓(𝑖,𝑘) is defined as above. Then

(1) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘,𝑙) if 𝜎 is infinite with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 or

(2) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘) if 𝜎 is finite.

Proof. We prove only (1) but in a stronger version. A similar proof can be given to prove (2). The proof proceeds by induction on 
the rules of the definition of translation. 
Base: for an atomic proposition 𝑝 ∈ 𝑃𝑟𝑜𝑝.

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ while (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙) iff 𝜎 ⊧𝑘 𝑝(𝑠𝑖) iff 𝑠𝑖[𝑝] = ⊤. So, (𝜎, 𝑖) ⊧𝑘 𝑝 iff (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙)
Induction: 
Suppose (𝜎, 𝑖) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙), (𝜎, 𝑖) ⊧𝑘 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙). We have,

1) (𝜎, 𝑖) ⊧𝑘 ¬𝑓 iff (𝜎, 𝑖) ̸⊧𝑘 𝑓 def

iff (𝜎, 𝑖) ̸⊧𝑘 𝑓(0,𝑘,𝑙) hypothesis 
iff (𝜎, 𝑖) ⊧𝑘 ¬𝑓(0,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (¬𝑓 )(0,𝑘,𝑙) def

2) (𝜎, 𝑖) ⊧𝑘 𝑓 ∨ 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑓 or (𝜎, 𝑖) ⊧𝑘 𝑔 def

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) or (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙) def

3) (𝜎, 𝑖) ⊧𝑘 ○𝑓 iff (𝜎, 𝑖) ⊧○𝑓 Lemma 1
iff (𝜎, 𝑖+ 1) ⊧ 𝑓 Def

iff (𝜎, 𝑖+ 1) ⊧ 𝑓(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧ (○𝑓 )(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (○𝑓 )(𝑖,𝑘,𝑙) Lemma 1

We do not need to consider 𝜀 and 𝜖
again here. When 𝑖 = 0 the Lemma 3 is proved. Now we come to prove an important conclusion 

formalized in Theorem 3.

Theorem 3. [𝑀,𝑓 ]𝑘 is satisfiable iff
The file is too long and its contents have been truncated.


#### Plugin (file_search):
Make sure to include fileciteturn12file2 in your response to cite this file, or to surface it as a link.

























































SAT-based bounded model checking for propositional projection temporal logic


Theoretical Computer Science 1049 (2025) 115368

Available online 6 June 2025
0304-3975/© 2025 Elsevier B.V. All rights are reserved, including those for text and data mining, AI training, and similar technologies.

Contents lists available at ScienceDirect

Theoretical Computer Science  

journal homepage: www.elsevier.com/locate/tcs

SAT-based bounded model checking for propositional projection 

temporal logic ✩

Zhenhua Duan a, Cong Tian a,∗, Nan Zhang a,∗, Chaofeng Yu a, Mengfei Yang b, Jia He a

a Institute of Computing Theory and Technology, Xidian University, Xi’an 710071, China
b China Academy of Space Technology, Beijing 100094, China

A R T I C L E I N F O A B S T R A C T 

Section Editor: Paul G. Spirakis

Handling Editor: Ding-Zhu Du

Keywords:

Propositional projection temporal logic

Bounded model checking

Rate monotonic scheduling

This paper presents a bounded model checking (BMC) approach for propositional projection 
temporal logic (PPTL). To this end, first PPTL is briefly introduced. Then, bounded semantics 
of PPTL is defined according to its semantics in logic theory. Further, a reduction method from 
BMC to SAT is given in detail. In addition, an example is presented to illustrate how the approach 
works. Finally, miniSAT is employed to solve the SAT based BMC problem by means of verifying 
RMS algorithm in detail. Our experience shows that SAT based BMC approach for PPTL proposed 
in the paper is useful and feasible.

1. Introduction

Model checking was firstly proposed by Clarke and Emerson [1] as well as Quielle and Sifakis [2] independently. As a trusted, 
strong and automatic verification technique, model checking has been widely used in many fields such as verification of hardware, 
software and communication protocols [3--5]. Model checking is a procedure used to check whether a property specified by a temporal 
logic formula 𝜙 is satisfied by a given system 𝑀 defined in a transition structure (𝑀 ⊧𝜙?). With temporal logics, linear-time temporal 
logic (LTL) [6] and branching-time temporal logic (CTL) [1] are popular in practice. In particular, they are usually used as description 
logics to specify properties of systems in model checking. However, for a given system, the number of states of the system increases 
exponentially with the increasing of the number of components in the system, leading to state explosion problem. To combat this 
problem, many optimization methods are put forward. Symbolic model checking based on binary decision diagrams (BDD) [7,8] 
aims at reduction in memory needed and high efficiency in model checking. They proposed symbolic model checker NuSMV [9]. 
Compositional model checking [10] optimizes model checking by dividing the model under consideration into several parts and 
conducts the verification of each part respectively to reduce the complexity of the checking process. Bounded model checking (BMC) 
[11] is an important progress in formalized verification after symbolic model checking [12]. It proves to be an efficient and successful 
approach. Several tools based on BMC such as CBMC [13], CPAChecker [14], and ESBMC [15] are developed to verify C programs. 
The main idea of BMC is to check whether a property is satisfied by a system with limitation that the searching length is bounded 
by a given integer 𝑘. If the property is not satisfied, an error is found. Otherwise, we cannot tell whether the system satisfies the 
property or not. In this case, we can consider increasing 𝑘, and perform the process of BMC again. Nevertheless, a deficiency of BMC 

✩ This research is supported by the NSFC Grant Nos. 62192734, 62172322, and 62272359.

* Corresponding authors.

E-mail addresses: zhhduan@mail.xidian.edu.cn (Z. Duan), ctian@mail.xidian.edu.cn (C. Tian), nanzhang@xidian.edu.cn (N. Zhang), cfyu@stu.xidian.edu.cn

(C. Yu), yangmf@bice.org.cn (M. Yang).

https://doi.org/10.1016/j.tcs.2025.115368

Received 8 January 2025; Received in revised form 13 April 2025; Accepted 30 May 2025 

http://www.ScienceDirect.com/
http://www.elsevier.com/locate/tcs
mailto:zhhduan@mail.xidian.edu.cn
mailto:ctian@mail.xidian.edu.cn
mailto:nanzhang@xidian.edu.cn
mailto:cfyu@stu.xidian.edu.cn
mailto:yangmf@bice.org.cn
https://doi.org/10.1016/j.tcs.2025.115368
http://crossmark.crossref.org/dialog/?doi=10.1016/j.tcs.2025.115368&domain=pdf
https://doi.org/10.1016/j.tcs.2025.115368


Theoretical Computer Science 1049 (2025) 115368

2

Z. Duan, C. Tian, N. Zhang et al. 

is its incompleteness because we cannot prove the absence of errors when all finite paths within 𝑘𝑚𝑎𝑥 are checked without finding 
any counterexample path. Instead, it can only confirm that the property being verified is satisfiable up to the specified bound of 𝑘𝑚𝑎𝑥 .

As the capabilities of SAT solvers continue to evolve, SAT-based BMC [16,17] typically encodes finite-length system paths and 
temporal logic formulas into Boolean formulas, reducing the search for counterexamples to a propositional satisfiability problem that 
can be solved using an SAT solver. Although SAT is proved to be an NP-complete problem, however, SAT solver works well in many 
practical applications with the DPLL algorithm [18]. Modern SAT solvers such as MiniSAT [19] can handle instances with hundreds 
of thousands of variables and millions of clauses. It seems plausible that SAT-based BMC has a greater advantage in verifying more 
complex multivariate systems than classical techniques based on BDDs. A variety of SAT-based bounded model checking detectors 
such as EBMC [20] are used in the verification of large-scale hardware and software systems.

Current SAT-based BMC algorithms utilize LTL or CTL to specify desired properties. The expressive power of both LTL and CTL 
is not full regular. There are at least two types of properties in practice that cannot be specified by LTL and CTL: (1) sometimes 
duration-related properties such as property P holds at the 50th state or 𝑃 holds after the 50th time unites and before the 100th 
time unites; (2) some periodic repetitive properties (Kleen closure) 𝑃 . So using LTL or CTL to describe the properties of systems is 
inadequate. In this paper, to more fully describe the properties of circuit designs and more convenient to construct the model, we 
utilize PPTL [21,22], a kind of temporal logic with full regular expressiveness [23,24], to describe the properties of a system.

With the community of projection temporal logic (PTL), plenty of logic laws [25] have been formalized and proved, and a decision 
procedure for checking satisfiability of PPTL formulas has also been given [26,27]. Further, a model checker based on SPIN for PPTL 
has been developed [28]. Therefore, full regular properties and time duration properties of systems can be automatically verified 
with SPIN. However, since the state explosion problem is a common problem for model checking, the model checker based on SPIN 
for PPTL also suffers from this problem. To combat it, we are motivated to investigate SAT based bounded model checking for PPTL 
in this paper. To do so, the bounded semantics of PPTL is defined, and some lemmas and theorems for building relationship between 
bounded model checking and the basic model checking are proved. Based on these basic theories, BMC for PPTL is reduced into SAT 
problem. To illustrate how our approach can be used to verify full regular properties of systems, an example for verifying feasibility of 
rate monotonic scheduling (RMS) algorithm [29] is presented in details. To realize our SAT based bounded model checking approach, 
Tseitin encoder technique and miniSAT solver are employed to build a prototype of bounded model checker based on NuSMV2.

The rest of the paper is organized as follows. PPTL is briefly introduced in section 2. In section 3, bounded model checking for 
PPTL is formalized in detail. Further, an example for verifying feasibility of RMS algorithm is demonstrated. In section 3, a framework 
of SAT based BMC for PPTL is outlined. The RMS algorithm is automatically verified using miniSAT with our prototype. Some related 
work are reviewed in section 6. In section 7 discusses the inherent incompleteness of BMC and the selection of 𝑘𝑚𝑎𝑥. Finally, the 
conclusion is drawn in section 8.

2. Propositional projection temporal logic

To study bounded model checking of interval based temporal logic (IBTL), we use proposition projection temporal logic (PPTL) 
as the underlying logic. The syntax and semantics of PPTL is briefly introduced in the following. The details of the logic can refer to 
[26].

2.1. Syntax:

PPTL comprises propositional logic and two primitive modal constructs used to reason about systems over time intervals. Let Prop
be a countable set of atomic propositions, and 𝑁 the set of natural numbers. The formulas of PPTL are inductively defined as follows:

𝑃 ∶∶= 𝑝 | ○ 𝑃 | ¬𝑃 | 𝑃1 ∨ 𝑃2 | (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑃

where 𝑝 ∈ 𝑃𝑟𝑜𝑝 and 𝑃 ,𝑃1,… , 𝑃𝑖,… , 𝑃𝑙,… , 𝑃𝑚 (for 1 ≤ 𝑖 ≤ 𝑙 ≤ 𝑚 and 𝑖, 𝑙,𝑚 ∈ 𝑁) are well-formed PPTL formulas. PPTL formulas 
consist of two basic temporal operators: next (○) and projection (𝑝𝑟𝑗). A formula is called a state formula if it contains no temporal 
operators, otherwise it is called a temporal formula.

2.2. Semantics:

Let 𝐵 = {⊤,⊥} be the set of boolean values. Let 𝜔 denote infinity. We consider the extended integer set 𝑁𝜔 =𝑁 ∪{𝜔} and extend 
the comparison operators, =, <, ≤, to 𝑁𝜔 by considering 𝜔 = 𝜔, and for all 𝑖 ∈ 𝑁 , 𝑖 < 𝜔,𝜔 = 𝜔 + 𝑖. Furthermore, we define ⪯ as 
≤ −{(𝜔,𝜔)}.

A state 𝑠𝑖 is a mapping from 𝑃𝑟𝑜𝑝 to 𝐵. An interval 𝜎 is a finite or infinite sequence of states, denoted by 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠|𝜎|⟩. 
The length, |𝜎|, of 𝜎 is 𝜔 if 𝜎 is infinite, and the number of states minus 1 if 𝜎 is finite. An interval that contains only one state is 
called a singleton interval ⟨𝑠0⟩, and its length |⟨𝑠0⟩| = 0. For convenience, we use a general notation 𝜎(𝑖..𝑗)(0 ≤ 𝑖 ⪯ 𝑗 ≤ |𝜎|) to denote 
the subinterval ⟨𝑠𝑖,… , 𝑠𝑗⟩ and 𝜎(𝑘)(0 ≤ 𝑘 ⪯ |𝜎|) to denote ⟨𝑠𝑘,… , 𝑠|𝜎|⟩. It becomes an infinite interval 𝜎(𝑖..𝜔) = ⟨𝑠𝑖,…⟩ when 𝑗 = 𝜔

while 𝜎(𝑖..𝑖) = ⟨𝑠𝑖⟩ becomes a singleton interval when 𝑖 = 𝑗. In some circumstances, we allow 𝑗 < 𝑖, in this case, 𝜎(𝑖..𝑗) = ε. Note that, ε
denotes void (for nothing) and its length |ε| is -1.

Now, we present the concatenation (⋅) operation on intervals. Let 𝜎1 and 𝜎2 be two intervals, the concatenation of two intervals 
𝜎1 and 𝜎2, denoted by 𝜎1 ⋅ 𝜎2 is the interval whose states are the states of 𝜎1 followed by the states of 𝜎2.



Theoretical Computer Science 1049 (2025) 115368

3

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 1. Projected Intervals. 

Fig. 2. Three cases of (𝑃1,… , 𝑃4) 𝑝𝑟𝑗 𝑄. (For interpretation of the colors in the figure(s), the reader is referred to the web version of this article.)

𝜎1 ⋅ 𝜎2 =

⎧⎪⎪⎨⎪⎪⎩

𝜎1, if |𝜎1| = 𝜔 or 𝜎2 = ε,

𝜎2, if 𝜎1 = ε,⟨𝑠0,… , 𝑠𝑖, 𝑠𝑖+1,… , 𝑠𝑗⟩, if 𝜎1 = ⟨𝑠0,… , 𝑠𝑖⟩ and 𝜎2 = ⟨𝑠𝑖+1,… , 𝑠𝑗⟩,
𝑗 ≤ 𝜔, |𝜎1| ≠ 𝜔.

It is straightforward that |𝜎1 ⋅ 𝜎2| = |𝜎1|+ |𝜎2| and for any interval 𝜎, ε ⋅ 𝜎 = 𝜎 ⋅ ε = 𝜎.

For a given interval 𝜎 = ⟨𝑠0, 𝑠1,…⟩, it is possible that some states can repeatedly appear in the sequence (stutter). To avoid the 
same successive state to produce different projected states, we define the projected interval:

𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚) = ⟨𝑠𝑡0 , 𝑠𝑡1 ,… , 𝑠𝑡𝑛 ⟩,
where 0 ≤ 𝑟0 ≤ 𝑟1 ≤ … 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ |𝜎| ≤ 𝜔, 𝑚 ∈ 𝑁 , and 𝑡0, 𝑡1,… , 𝑡𝑛 are obtained from states’ subscripts 𝑟0, 𝑟1,… , 𝑟𝑚 by deleting 
all duplicates. That is, 𝑡0,… , 𝑡𝑛 is the longest strictly increasing subsequence of 𝑟0, 𝑟1,… , 𝑟𝑚. Note that 𝑟𝑚 can be 𝜔, in this case, 
𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1,𝜔) = 𝜎 ↓ (𝑟0, 𝑟1,… , 𝑟𝑚−1). Moreover, it is necessary and reasonable to define that 𝜎 ↓ () = 𝜀. Some projected 
intervals are given below (See Fig. 1).

(a) ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,3,4,4,4,6) = ⟨𝑠0,… , 𝑠8⟩ ↓ (0,3,4,6) = ⟨𝑠0, 𝑠3, 𝑠4, 𝑠6⟩
(b) ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0,0) = ⟨𝑠0, 𝑠1, 𝑠2⟩ ↓ (0) = ⟨𝑠0⟩
(c) ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47,47,𝜔) = ⟨𝑠0, 𝑠1,…⟩ ↓ (0,21,47) = ⟨𝑠0, 𝑠21, 𝑠47⟩

Projected interval is obtained by taking the endpoints (rendezvous points) of the intervals over which 𝑃1 ,… , 𝑃𝑚 are interpreted 
in the projection construct. In order to interpret the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 intuitively, we need to work out a useful interval 𝜎𝑞

as follows:

Let 𝜎 = ⟨𝑠0, 𝑠1,… , 𝑠𝑚,… , 𝑠𝑗⟩ (𝑗 may be 𝜔) be an interval over which the formula (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 is interpreted while 𝑃𝑖 is 
interpreted over a subinterval 𝜎(𝑟𝑖−1 ..𝑟𝑖) = ⟨𝑠𝑟𝑖−1 ,… , 𝑠𝑟𝑖⟩(1 ≤ 𝑖 ≤ 𝑚). There are three cases we need to take into account: as shown in 
Fig. 2, Case 1: 𝑄 terminates before 𝑃𝑚, Case 2: 𝑄 and 𝑃𝑚 terminate at the same state, and Case 3: 𝑄 continues after the termination 
of 𝑃𝑚 (see red color sequence).

Thus, we define 𝜎𝑞 as follows:

𝜎(𝑟𝑚+1..𝑗) =

{
< 𝑠(𝑟𝑚+1), ..., 𝑠𝑗 >, if 𝑟𝑚 < 𝑗,

ε, if 𝑟𝑚 = 𝑗.

𝜎𝑞 = 𝜎 ↓ (𝑟0,… , 𝑟𝑚) ⋅ 𝜎(𝑟𝑚+1..𝑗). (1)



Theoretical Computer Science 1049 (2025) 115368

4

Z. Duan, C. Tian, N. Zhang et al. 

Table 1
Derived formulas.

A1 𝜀
def
= ¬○⊤ A2 𝜖def= ○⊤

A3 ⨀
𝑃

def
= 𝜀 ∨○𝑃 A4 𝑃 ;𝑄

def
= (𝑃 ,𝑄) 𝑝𝑟𝑗 𝜀

A5 ◊ 𝑃
def
= ⊤;𝑃 A6 □𝑃

def
= ¬◊¬𝑃

A7 𝑓𝑖𝑛
def
= ◊𝜀 A8 𝑖𝑛𝑓

def
= ¬𝑓𝑖𝑛

A9

{
○0𝑃

def
= 𝑃

○𝑛𝑃
def
= ○(○𝑛−1𝑃 )(𝑛 > 0)

A10 𝑃 || 𝑄 def
= (𝑃 ;⊤) ∧𝑄 ∨ 𝑃 ∧ (𝑄;⊤)

∨𝑃 ∧𝑄 ∧□

𝜖

A11 𝑙𝑒𝑛(𝑛)
def
= ○𝑛𝜀 (𝑛 ≥ 0)

𝜎𝑞 is concatenated by two parts, which will be of great convenience to illustrate the three cases in the definition of the 𝑝𝑟𝑗 operator.

PPTL formulas are interpreted over intervals. An interpretation  = (𝜎,𝑘, 𝑗) is a subinterval ⟨𝑠𝑘,… , 𝑠𝑗⟩ of 𝜎 with the current state 
being 𝑠𝑘. The semantics of PPTL formulas is inductively defined as a satisfaction relation below. Note that we also use notation 𝜎 ⊧ 𝑃

if 𝜎(0, |𝜎|) ⊧ 𝑃 .

(1)  ⊧ 𝑝 iff 𝑠𝑘[𝑝] = ⊤.

(2)  ⊧○𝑃 iff 𝑘 < 𝑗 and (𝜎,𝑘+ 1, 𝑗) ⊧ 𝑃 .

(3)  ⊧ ¬𝑃 iff  ̸⊧ 𝑃 .

(4)  ⊧ 𝑃 ∨𝑄 iff  ⊧ 𝑃 or  ⊧ 𝑄.

(5)  ⊧ (𝑃1,… , 𝑃𝑚) 𝑝𝑟𝑗 𝑄 iff there exist 𝑚 extended integers 𝑘 = 𝑟0 ≤ 𝑟1 ≤ … ≤ 𝑟𝑚−1 ⪯ 𝑟𝑚 ≤ 𝑗 such that (𝜎, 𝑟𝑙−1, 𝑟𝑙) ⊧ 𝑃𝑙 for all 
1 ≤ 𝑙 ≤𝑚, and 𝜎𝑞 ⊧ 𝑄 (i.e. (𝜎𝑞,0, |𝜎𝑞|) ⊧ 𝑄).

Satisfaction and Validity: A formula 𝑝 is satisfied by an interval 𝜎, denoted by 𝜎 ⊧ 𝑝, if (𝜎,0, |𝜎|) ⊧ 𝑝. A formula 𝑝 is called satisfiable 
if 𝜎 ⊧ 𝑝 for some 𝜎. A formula 𝑝 is valid, denoted by ⊧ 𝑝, if 𝜎 ⊧ 𝑝 for all 𝜎.

Derived formula: The abbreviations ⊤, ⊥, ∧, → and ↔ are defined as usual. In particular, ⊤
def
= 𝑃 ∨ ¬𝑃 and ⊥

def
= 𝑃 ∧ ¬𝑃 , for any 

formula 𝑃 . Some derived formulas in PPTL are defined in Table 1.

2.3. Normal form

Normal Form (NF) [26] is a useful notation in our methods. We assume 𝑄𝑝 is the set of atomic propositions appearing in the PPTL 
formula 𝑄. Then, the NF can be defined as follows:

Definition 1. Normal Form of 𝑄:

𝑁𝐹 (𝑄) ≡ ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) ∨ ∨𝑛

𝑖=1(𝑄𝑐𝑖 ∧○𝑄′
𝑖
)

To simplify the proof and expressiveness, we sometimes use 𝑄𝑒 ∧ 𝜀 instead of ∨𝑛0
𝑗=1(𝑄𝑒𝑗 ∧ 𝜀) and apply ∨𝑟

𝑖=1(𝑄𝑖 ∧○𝑄′
𝑖
) to replace 

∨𝑛
𝑖=1(𝑄𝑐𝑖 ∧○𝑄′

𝑖
). Thus,

𝑁𝐹 (𝑄) ≡𝑄𝑒 ∧ 𝜀 ∨ ∨𝑟
𝑖=1(𝑄𝑖 ∧○𝑄′

𝑖
)

where 𝑄𝑒 and 𝑄𝑖 are state formulas.

Theorem 1. Any PPTL formula 𝑃 can be rewritten into its Normal Form.

The proof of this theorem can be found in [26].

Example 1. Given a PPTL formula 𝑓 , 𝑓 ≡ (𝑝 ; 𝑞) 𝑝𝑟𝑗 𝑟, we can get

𝑁𝐹 (𝑓 ) ≡ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧ 𝜀) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; 𝑞)) ∨ (𝑟 ∧ 𝑞 ∧ 𝑝 ∧○⊤) ∨ (𝑟 ∧ 𝑝 ∧○(⊤; (𝑞;⊤)))

3. Principle of SAT-based bounded model checking with PPTL

In this section, we investigate the bounded model checking of PPTL based on the theory presented in section 2. To do this, we 
first establish the basic theory, bounded semantics, on bounded model checking of PPTL. Then we introduce a new approach of 
bounded model checking for PPTL. Since each PPTL formula can be transformed into an equivalent formula in NF, unlike LTL and 
CTL formulas [12,30], we do not need to deal with all types of PPTL formulas in the bounded semantics. As a result, we need only 
consider formulas with ∨, ¬, and ○ operators as well as 𝜀 and 𝜖

. In the following, we define the bounded semantics of PPTL formulas. 
Let 𝜎 be an interval and 𝑃 a PPTL formula.



Theoretical Computer Science 1049 (2025) 115368

5

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 3. 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝. 

3.1. Bounded semantics

In this subsection, we first define Kripke structure, then we define bounded semantics of PPTL formulas.

Definition 2. A Kripke structure M is a quadruple 𝑀 = (𝑆,𝐼, 𝑇 ,𝐿) where 𝑆 is the set of sates, 𝐼 ⊆ 𝑆 is the set of initial states, 
𝑇 ⊆ 𝑆 × 𝑆 is the transition relation and 𝐿 ∶ 𝑆 → 𝑃 (𝐴) is the labeling function, where 𝐴 is the set of atomic propositions and 𝑃 (𝐴)
denotes the powerset over 𝐴.

We use Kripke structure to model systems, and PPTL formulas to define properties of systems. A path in a Kripke structure can 
be treated as an interval. Since a path with a Kripke structure can be finite or infinite so an interval can also be finite or infinite. 
Therefore, in the following, we give the definition of 𝑘− 𝑙𝑜𝑜𝑝 in an interval.

Definition 3. k-loop: For 𝑙, 𝑘 ∈ 𝑁0 and 𝑙 ≤ 𝑘, if there is a translation from 𝑠𝑘 to 𝑠𝑙 in 𝜎 and 𝜎 = ⟨𝑠0,… , 𝑠𝑙−1) ⋅ ⟨𝑠𝑙,… , 𝑠𝑘⟩𝜔, we call 
interval 𝜎 a (k, l)-loop. If there exist 𝑘, 𝑙, 𝑘 ≥ 𝑙 ≥ 0 such that 𝜎 is a (k, l)-loop, we call 𝜎 a k-loop.

Obviously, if 𝜎 is an infinite interval with loop, it must be a 𝑘 − 𝑙𝑜𝑜𝑝 for some 𝑘 ∈𝑁0. Now we can define the successor of state 
𝑠𝑖 over an interval 𝜎 by 𝑠𝑢𝑐𝑐(𝑖) below:

𝑠𝑢𝑐𝑐(𝑖) =
⎧⎪⎨⎪⎩

𝑖+ 1 if 𝑖 < 𝑘

𝑙 if 𝑖 = 𝑘 and 𝜎 is an infinite interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝

𝑘+ 1 if 𝑖 = 𝑘 and 𝜎 is a finite interval 

With bounded model checking of PPTL, given a bound 𝑘 ∈𝑁0, an interpretation is a pair ′ = (𝜎, 𝑖), where 𝜎 is an interval, 𝑖 an 
integer and 0 ≤ 𝑖 ≤ 𝑘 ≤ |𝜎|. We use the notation (𝜎, 𝑖) ⊧𝑘 𝑃 to represent that formula 𝑃 is interpreted and satisfied over the subinterval 
< 𝑠𝑖,… , 𝑠𝑘 > of 𝜎 with the current state being 𝑠𝑖. In terms of the semantics of PPTL formulas given in section 2, (𝜎, 𝑖) ⊧𝑘 𝑃 is equal to 
(𝜎, 𝑖, 𝑘) ⊧ 𝑃 , thus (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 .

The bounded satisfaction relation ⊧𝑘 is inductively defined as follows:

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition

(𝜎, 𝑖) ⊧𝑘 ¬𝑃 iff (𝜎, 𝑖) ̸⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝑃1 ∨ 𝑃2 iff (𝜎, 𝑖) ⊧𝑘 𝑃1 or (𝜎, 𝑖) ⊧𝑘 𝑃2
(𝜎, 𝑖) ⊧𝑘 ○𝑃 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑃

(𝜎, 𝑖) ⊧𝑘 𝜀 iff 𝑖 = 𝑘

(𝜎, 𝑖) ⊧𝑘

𝜖

iff 𝑖 < 𝑘

A formula 𝑃 is satisfied with bound 𝑘 by an interval 𝜎, denoted by 𝜎 ⊧𝑘 𝑃 , if (𝜎,0) ⊧𝑘 𝑃 . Since (𝜎, 𝑖) ⊧𝑘 𝑃 iff (𝜎, 𝑖, 𝑘) ⊧ 𝑃 , we have 
𝜎 ⊧𝑘 𝑃 iff (𝜎,0, 𝑘) ⊧ 𝑃 .

As any PPTL formula 𝑃 can be rewritten into its normal form, the above definition about satisfaction relation in bounded semantics 
of PPTL is sound.

3.2. Bounded model checking

According to the structure of interval 𝜎, two basic lemmas are given below:

Lemma 1. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝 (Fig. 3). Then 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓 .

Proof. To prove Lemma 1, we first prove a stronger conclusion given below:

(𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘)

Thus, Lemma 1 can be concluded by setting 𝑖 = 0. Now, we prove the above conclusion by induction on the structure of formula 𝑓 :

Base case:

𝑓 ≡ 𝑝 ∈ 𝑃𝑟𝑜𝑝: (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤ and (𝜎, 𝑖, |𝜎|) ⊧ 𝑝 iff 𝑠𝑖[𝑝] = ⊤, so we have (𝜎, 𝑖, 𝑘) ⊧ 𝑝 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑝.



Theoretical Computer Science 1049 (2025) 115368

6

Z. Duan, C. Tian, N. Zhang et al. 

Fig. 4. 𝜎 is a finite interval. 

Inductive cases:

1. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Then, we have, (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 . Further, 
(𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, 𝑘) ̸⊧𝑘 𝑓 and (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ̸⊧ 𝑓 , leading to (𝜎, 𝑖, 𝑘) ⊧ ¬𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ ¬𝑓 .

2. Suppose for any PPTL formula 𝑓 , (𝜎, 𝑖, 𝑘) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓 (0 ≤ 𝑖 ≤ 𝑘). Since 𝜎 is a 𝑘− 𝑙𝑜𝑜𝑝, so, 𝑠𝑢𝑐𝑐(𝑖) ≤ 𝑘 < |𝜎|. Then, by 
hypothesis, we have,

(𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 . By the definitions of semantics, (𝜎, 𝑠𝑢𝑐𝑐(𝑖), 𝑘) ⊧ 𝑓 iff (𝜎, 𝑠𝑢𝑐𝑐(𝑖)) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 ○𝑓

iff (𝜎, 𝑖, 𝑘) ⊧○𝑓 and (𝜎, 𝑠𝑢𝑐𝑐(𝑖), |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖+ 1, |𝜎|) ⊧ 𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 , so (𝜎, 𝑖, 𝑘) ⊧○𝑓 iff (𝜎, 𝑖, |𝜎|) ⊧○𝑓 .

3. Suppose for any PPTL formulas 𝑓1 and 𝑓2, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 and (𝜎, 𝑖, 𝑘) ⊧ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓2. Then, by the 
definitions of bounded semantics and model semantics, (𝜎, 𝑖, 𝑘) ⊧ 𝑓1 ∨ 𝑓2 iff (𝜎, 𝑖, |𝜎|) ⊧ 𝑓1 ∨ 𝑓2. □

Note that we do not need to deal with 𝜀 and 𝜖

in the above inductive cases since 𝜀 ≡ ¬○⊤ and 𝜖

≡○⊤.

Lemma 2. Let f be a PPTL formula, and 𝜎 a finite interval (Fig. 4). Then 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 .

Proof. Since 𝜎 is a finite interval, so |𝜎| ∈𝑁0.

𝜎 ⊧ 𝑓 ⇔ (𝜎,0, |𝜎|) ⊧ 𝑓

⇔ (𝜎,0, 𝑘) ⊧ 𝑓 ∧ 𝑘 = |𝜎|
⇒ ∃𝑘,𝑘 ≥ 0, (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0, 𝜎 ⊧𝑘 𝑓 □

Theorem 2. Suppose a system is described by a Kripke structure M, and some property is defined by a PPTL formula 𝑓 . Let 𝑀 be the set 
of all intervals generated in M. We define 𝑀 ⊧ ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 as well as 𝑀 ⊧𝑘 ∃𝑓 iff ∃𝜎 ∈ 𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . Then we have 
𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 .

Proof. We need prove that ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧ 𝑓 iff ∃𝜎 ∈𝑀 𝑎𝑛𝑑 𝜎 ⊧𝑘 𝑓 . To do so, we consider intervals in 𝑀 as infinite or finite ones 
respectively.

1. Suppose 𝜎 is infinite, there must be an integer 𝑘 ≥ 0 that makes 𝜎 a 𝑘− 𝑙𝑜𝑜𝑝. By Lemma 1:

𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧ 𝑓

we have,

𝑀 ⊧ ∃𝑓 iff ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓

2. Suppose interval 𝜎 is finite, i.e., |𝜎| =𝑚 ∈𝑁0.

“ ⇒ ” ∶𝑀 ⊧ ∃𝑓 ⇔ ∃𝜎 ∈𝑀 ∧ 𝜎 ⊧ 𝑓 ⇒ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,Σ ⊧𝑘 ∃𝑓 (Lemma 2)

“ ⇐ ” ∶ ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ 𝜎 ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0) ⊧𝑘 𝑓

⇔ ∃𝑘,𝑘 ≥ 0,∃𝜎 ∈𝑀 ∧ (𝜎,0, 𝑘) ⊧ 𝑓

Let 𝜎′ =< 𝑠0, 𝑠1,… , 𝑠𝑘 >, we have (𝜎′,0, 𝑘) ⊧ 𝑓 . Since 𝜎′ is a subinterval 

of 𝜎 and |𝜎′| = 𝑘, hence, ∃𝜎′ ∈𝑀 and 𝜎′ ⊧ 𝑓 , leading to 𝑀 ⊧ ∃𝑓.

As a result, ∃𝑘,𝑘 ≥ 0,𝑀 ⊧𝑘 ∃𝑓 ⇒𝑀 ⊧ ∃𝑓. □

3.3. Reducing bounded model checking with PPTL to SAT

Given a finite state transition system 𝑀 (a Kripke structure or NFG), the property of the system in terms of a PPTL formula 𝑓 , and 
a bound 𝑘, then the procedure of BMC can be described as a process for constructing a proposition formula [𝑀,𝑓 ]𝑘. Let ⟨𝑠0,… , 𝑠𝑘⟩ be 
a subinterval of interval 𝜎. The definition of formula [𝑀,𝑓 ]𝑘 consists of two components: 𝑀𝑘, the first component, is a propositional 
formula that constrains ⟨𝑠0,… , 𝑠𝑘⟩ to be a valid interval starting from an initial state; 𝑋𝑘 , the second component, a propositional 



Theoretical Computer Science 1049 (2025) 115368

7

Z. Duan, C. Tian, N. Zhang et al. 

formula that constrains 𝜎 to satisfy 𝑓 with bound 𝑘. To define the second component, we first give the definition of 𝑙𝑜𝑜𝑝 𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛, 
which is a propositional formula that is evaluated to true only if the interval 𝜎 contains a loop; then we give some translation rules 
for formulas.

Definition 4. For a Kripke structure M, and k ≥ 0,

𝑀𝑘

def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1)

Loop condition:

𝐿(𝑘,𝑙)
def 
= 𝑇 (𝑠𝑘, 𝑠𝑙)  (0 ≤ 𝑙 ≤ 𝑘)

𝐿𝑘

def 
= ∨𝑘

𝑙=0 𝐿(𝑘,𝑙)

Let 𝑝 be an atomic proposition, and 𝑓 , 𝑔 be PPTL formulas, 𝜎 an interval with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝, 𝑠𝑖 the current state, and 𝑘 the bound, 
where 0 ≤ 𝑖, 𝑙, 𝑘 ≤ |𝜎|, 𝑖, 𝑙 ≤ 𝑘. The translation of a PPTL formula is given below:

k-loop: Translation 𝑓 (𝑖, 𝑘, 𝑙) of a PPTL formula 𝑓 over an infinite interval 𝜎 with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 is inductively defined as follows.

𝑝(𝑖,𝑘,𝑙)
def 
= 𝑝(𝑠𝑖) if 𝑝 ∈ 𝑃𝑟𝑜𝑝 is an atomic proposition, meaning 𝑠𝑖[𝑝]

(¬𝑓 )(𝑖,𝑘,𝑙)
def 
= ¬𝑓(𝑖,𝑘,𝑙)

(𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙)

(○𝑓 )(𝑖,𝑘,𝑙)
def 
= 𝑓(𝑠𝑢𝑐𝑐(𝑖),𝑘,𝑙)

𝜀(𝑖,𝑘,𝑙)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘,𝑙)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

For the translation presented above, a new propositional variable is introduced for each intermediate formula 𝑒(𝑖,𝑘,𝑙), where 𝑒 is a 
sub-formula of PPTL formula 𝑓 and 0 ≤ 𝑖 ≤ 𝑘 and 𝑙 indicates the existence of (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝. If 𝑒 is an atomic proposition or its negation, 
𝑒(𝑖,𝑘,𝑙) is substituted by a boolean variable with the truth-value at state 𝑠𝑖. Otherwise, 𝑒(𝑖,𝑘,𝑙) indicates a propositional formula whose 
satisfiability should be considered over the interval (𝑠𝑖,… , 𝑠𝑘).

no loop: Translation 𝑓 (𝑖, 𝑘) of a PPTL formula 𝑓 for a finite interval 𝜎 (with no loop).

𝑝(𝑖,𝑘)
def 
= 𝑝(𝑠𝑖)

(¬𝑓 )(𝑖,𝑘)
def 
= ¬𝑓(𝑖,𝑘)

(𝑓 ∨ 𝑔)(𝑖,𝑘)
def 
= 𝑓(𝑖,𝑘) ∨ 𝑔(𝑖,𝑘)

(○𝑓 )(𝑖,𝑘)
def 
= 𝑓(𝑖+1,𝑘)

𝑓(𝑘+1,𝑘)
def 
= ⊥

𝜀(𝑖,𝑘)
def 
= 

{
⊥ 𝑖 < 𝑘

⊤ 𝑖 = 𝑘

𝜖

(𝑖,𝑘)
def 
= 

{
⊤ 𝑖 < 𝑘

⊥ 𝑖 = 𝑘

When the intermediate formula 𝑒(𝑖,𝑘) appears in a PPTL formula for a finite interval (with no loop), the explanations are similar to 
the ones for a PPTL formula with an interval with (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 and omitted here.

General translation (BMC to SAT): 

𝑋𝑘

def 
= (¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))

[𝑀,𝑓 ]𝑘
def 
= 𝑀𝑘 ∧𝑋𝑘

i.e.:

[𝑀,𝑓 ]𝑘
def 
= 𝐼(𝑠0) ∧ ∧𝑘−1

𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ [(¬𝐿𝑘 ∧ 𝑓(0,𝑘)) ∨ ∨𝑘
𝑙=0(𝐿(𝑘,𝑙) ∧ 𝑓(0,𝑘,𝑙))]



Theoretical Computer Science 1049 (2025) 115368

8

Z. Duan, C. Tian, N. Zhang et al. 

As we can see, the right side of the definition can be divided into two parts: the first part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (¬𝐿𝑘 ∧ 𝑓(0,𝑘))

indicates an interval with no loop and the translation without loop is used; the second part 𝐼(𝑠0) ∧ ∧𝑘−1
𝑖=0 𝑇 (𝑠𝑖, 𝑠𝑖+1) ∧ (∨𝑘

𝑙=0(𝐿(𝑘,𝑙) ∧
𝑓(0,𝑘,𝑙))) presents that an interval with a 𝑘 − 𝑙𝑜𝑜𝑝 and all possible starting points 𝑙 of a loop and the translation for a 𝑘 − 𝑙𝑜𝑜𝑝 is 
conjoined with the corresponding loop condition 𝐿(𝑘,𝑙).

Lemma 3. Let 𝑘 ∈𝑁0, 𝑓 be a PPTL formula and 𝜎 an interval. The translation 𝑓(𝑖,𝑘,𝑙) or 𝑓(𝑖,𝑘) is defined as above. Then

(1) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘,𝑙) if 𝜎 is infinite with a (𝑘, 𝑙) − 𝑙𝑜𝑜𝑝 or

(2) 𝜎 ⊧𝑘 𝑓 iff 𝜎 ⊧𝑘 𝑓(𝑖,𝑘) if 𝜎 is finite.

Proof. We prove only (1) but in a stronger version. A similar proof can be given to prove (2). The proof proceeds by induction on 
the rules of the definition of translation. 
Base: for an atomic proposition 𝑝 ∈ 𝑃𝑟𝑜𝑝.

(𝜎, 𝑖) ⊧𝑘 𝑝 iff 𝑠𝑖[𝑝] = ⊤ while (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙) iff 𝜎 ⊧𝑘 𝑝(𝑠𝑖) iff 𝑠𝑖[𝑝] = ⊤. So, (𝜎, 𝑖) ⊧𝑘 𝑝 iff (𝜎, 𝑖) ⊧𝑘 𝑝(𝑖,𝑘,𝑙)
Induction: 
Suppose (𝜎, 𝑖) ⊧𝑘 𝑓 iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙), (𝜎, 𝑖) ⊧𝑘 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙). We have,

1) (𝜎, 𝑖) ⊧𝑘 ¬𝑓 iff (𝜎, 𝑖) ̸⊧𝑘 𝑓 def

iff (𝜎, 𝑖) ̸⊧𝑘 𝑓(0,𝑘,𝑙) hypothesis 
iff (𝜎, 𝑖) ⊧𝑘 ¬𝑓(0,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (¬𝑓 )(0,𝑘,𝑙) def

2) (𝜎, 𝑖) ⊧𝑘 𝑓 ∨ 𝑔 iff (𝜎, 𝑖) ⊧𝑘 𝑓 or (𝜎, 𝑖) ⊧𝑘 𝑔 def

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) or (𝜎, 𝑖) ⊧𝑘 𝑔(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧𝑘 𝑓(𝑖,𝑘,𝑙) ∨ 𝑔(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (𝑓 ∨ 𝑔)(𝑖,𝑘,𝑙) def

3) (𝜎, 𝑖) ⊧𝑘 ○𝑓 iff (𝜎, 𝑖) ⊧○𝑓 Lemma 1
iff (𝜎, 𝑖+ 1) ⊧ 𝑓 Def

iff (𝜎, 𝑖+ 1) ⊧ 𝑓(𝑖,𝑘,𝑙) hypothesis

iff (𝜎, 𝑖) ⊧ (○𝑓 )(𝑖,𝑘,𝑙) def

iff (𝜎, 𝑖) ⊧𝑘 (○𝑓 )(𝑖,𝑘,𝑙) Lemma 1

We do not need to consider 𝜀 and 𝜖
again here. When 𝑖 = 0 the Lemma 3 is proved. Now we come to prove an important conclusion 

formalized in Theorem 3.

Theorem 3. [𝑀,𝑓 ]𝑘 is satisfiable iff
The file is too long and its contents have been truncated.


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
对，你这个问题抓到了**两个不同的“区间”**，所以容易混：

- 一个是**最外层** `(... ) prj r` 产生的投影区间 $\sigma_q$
- 一个是**里层** $p;q$，而它其实又等于 $(p,q) prj \varepsilon$

  所以答案是：

**“当前状态满足 $r$”说的是最外层投影区间 $\sigma_q$ 的起点；它不是在说‘$r$ 后续状态的开始’。** 原子命题的语义只是“当前状态上 $r$ 为真”，即 $\mathcal I \models r \iff s\_k\[r]=\top$。同时，projection 的语义要求的是 $\sigma\_q \models Q$，这里 $Q=r$，所以确实是在检查**最外层投影区间的第一个状态\*\*。fileciteturn12file0

接着说你第二问：

**它不等于“$(p,q)$ 这个投影区间的结束”，但在某些分支里，它可以和那个结束点重合。**\
原因是：里层顺序算子定义为

$
p;q \equiv (p,q)\ prj \varepsilon
$

而 $\varepsilon$ 的意思是“当前已经是最后一个状态”。所以里层 $p;q$ 关注的是：由 $p,q$ 构造出来的那个投影区间是否**在当前就结束**。这和最外层 `prj r` 检查的“当前起点是否满足 $r$”不是同一件事。fileciteturn12file0turn12file1

你可以这样分层理解：

先看**最外层**  
$
(p;q)\ prj r
$
它要求：把前件 $p;q$ 解释完以后，构造出最外层的 $\sigma_q$，并且这个 $\sigma_q$ 满足 $r$。而 $r$ 是原子命题，所以只检查 $\sigma_q$ 的**第一个状态**。fileciteturn12file0

再看**里层**  
$
p;q
$
它不是原子命题，而是派生公式：
$
p;q \equiv (p,q)\ prj \varepsilon
$
这里 $\varepsilon$ 表示“结束”，所以里层关心的是：由 $p$ 段、$q$ 段形成的那个投影区间，是否**正好在这里收尾**。fileciteturn12file0turn12file1

所以两句话分别对应：

- **$r$**：看“最外层投影区间从哪里开始”
- **$\varepsilon$**：看“里层顺序组合在哪里结束”

这两个位置**可能相同，也可能不同**。论文在解释 $(P_1,\dots,P_m) prj Q$ 时专门说了三种情况：$Q$ 可能在 $P_m$ 之前结束、和 $P_m$ 同时结束、或者在 $P_m$ 之后继续，因此专门定义了
$
\sigma_q=\sigma \downarrow (r_0,\dots,r_m)\cdot \sigma(r_m+1..j)
$
来处理这种“起点/终点不一定重合”的情况。fileciteturn12file0

所以，回到你这句：

> 当前状态满足r，这个状态是r后续状态的开始对吗，那是(p,q)这个投影区间的结束吗？

更准确地改写成：

**当前状态满足 $r$，指的是最外层 `prj r` 所得到的投影区间的起点；它不是“$r$ 后续状态的开始”这种说法。这个点也不必然是里层 $(p,q) prj \varepsilon$ 的结束点，但在某些退化或重合的情形下，二者可以落在同一个状态上。**

如果你愿意，我下一条可以直接给你画一个**三层对应图**：原区间、里层 $(p,q)$ 的投影区间、最外层 `prj r` 的投影区间，帮你把“起点”和“终点”彻底对齐。


#### You:
那这三个继续项是否对应着 当前状态r与 (p,q)区间的对应关系，r对应的状态在p前，r状态在pq之间，r状态在q后？

#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
\[Unsupported Content]


#### ChatGPT:
不完全是。**这三个继续项不能简单理解成“$r$ 在 $p$ 前 / 在 $p,q$ 之间 / 在 $q$ 后”**。更准确地说，它们对应的是：

> 在公式 $(p;q)\ prj\ r$ 成立时，**当前这一步已经完成了哪些局部要求**，以及**剩余的时序任务还要怎么往后继续**。

也就是它们区分的核心是：

- 当前点上，$p,q,r$ 哪些已经被当前状态承担了
- 后面还剩下什么结构要在未来完成

而不是单纯给 $r$ 在原区间里排一个“前中后”的线性位置。

---

## 一、先看这三个继续项本身

Example 1 的三个继续项是：

$
(r\land p)\land \circ(\top;q)
$

$
(r\land q\land p)\land \circ\top
$

$
(r\land p)\land \circ(\top;(q;\top))
$

它们共同点是：

- 当前状态都要求 $r$
- 当前状态都要求 $p$
- 只有第二项还要求当前状态也满足 $q$

差别主要在 `○` 后面的**剩余公式**不同。fileciteturn10file2turn12file0

---

## 二、为什么不能直接解释成“r 在 p 前 / 中 / 后”

因为 $r$ 不是一个“位置标记点”，而是一个**原子命题**。  
原子命题 $r$ 的语义只是：

$
(\sigma,k,j)\models r \iff s_k[r]=\top
$

也就是说，**当前状态满足 $r$**。它不是说“有一个专门叫 r 的状态在某个地方”。fileciteturn12file0

所以“$r$ 在 $p$ 前面”这种说法本身就容易误导，因为：

- $p,q,r$ 都是命题
- 它们可以在**同一个状态**上同时为真
- 不是三个互斥的时间点

例如第二个继续项

$
r\land q\land p\land \circ\top
$

就明确说明：**当前同一个状态**同时满足 $r,p,q$。  
这已经说明它们不是简单排成“前中后”三个位置。

---

## 三、那三个继续项更接近什么含义

更接近下面这三种“当前—未来分工”：

### 第一项
$
(r\land p)\land \circ(\top;q)
$

意思是：

- 当前状态已经承担了 $r$ 和 $p$
- 但 $q$ 还没在当前完成
- 未来还要继续把 $q$ 补上

所以它更像：

> **当前起点已经满足最外层的 $r$ 和里层顺序的开头 $p$，但后半段 $q$ 还要往后完成。**

---

### 第二项
$
(r\land q\land p)\land \circ\top
$

意思是：

- 当前状态已经把 $r,p,q$ 都承担了
- 后面不再有实质要求，只剩 $\top$

它更像：

> **所有关键条件都在当前点同时凑齐了。**

这是一个“完全就绪，只是形式上还属于继续项”的分支。

---

### 第三项
$
(r\land p)\land \circ(\top;(q;\top))
$

意思是：

- 当前状态仍然只承担 $r$ 和 $p$
- 但未来的剩余结构比第一项更长、更绕
- $q$ 会在更后面才完成

所以它更像：

> **当前只完成开头，$q$ 不是马上补上，而是在更长的后续结构里出现。**

---

## 四、如果硬要和“位置关系”做一个近似类比

只能非常谨慎地近似说：

- 第一项：$q$ 还在后面，不在当前
- 第二项：$q$ 就在当前
- 第三项：$q$ 在更后面，而且后续结构更长

但这仍然不是“$r$ 在 $p$ 前 / 中 / 后”。

因为在这三个项里，**$r$ 都在当前状态成立**，并没有移动位置；变化的是：

- $q$ 是否已经在当前点完成
- 以及剩余的顺序结构有多长

---

## 五、为什么你会产生“r 前中后”的感觉

因为你把：

$
(p;q)\ prj\ r
$

想成了“先有 $p,q$ 组成一个区间，然后 $r$ 再去贴到那个区间的某个位置上”。

但更准确的语义是：

- 先通过前件构造投影区间
- 再要求这个投影区间满足 $r$

  而对原子命题 $r$ 来说，“满足 $r$”只检查**投影区间的当前起点**。fileciteturn12file0

所以从 NF 角度看，$r$ 基本上总是被抽到“当前状态条件”里，而不是被拿去和 $p,q$ 做一个单独的前中后位置比较。

---

## 六、一个更正确的总结

你这三个继续项更适合理解成：

### 继续项 1

当前点承担 $r,p$，未来较快补上 $q$


### 继续项 2

当前点直接承担 $r,p,q$，未来无实质任务

### 继续项 3

当前点承担 $r,p$，但 $q$ 要在更长的未来结构里完成

这三种分支体现的是：

> **当前义务与未来义务如何分配**

而不是：

> **$r$ 在 $p,q$ 结构中的空间位置前中后**

---

## 七、一句话回答你

**不是。三个继续项不应理解成“$r$ 在 $p$ 前、在 $p,q$ 之间、在 $q$ 后”，因为 $r$ 是当前状态上成立的原子命题，不是单独的时间位置；这三个继续项真正区分的是：当前状态已经承担了哪些条件，以及剩余的 $q$ 相关时序结构要在未来怎样完成。** fileciteturn10file2turn12file0

下一步最有帮助的是我把这三个继续项分别画成三条时间线，用“当前点 / 下一步 / 后续区间”标出来。
