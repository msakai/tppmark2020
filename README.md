# TPPmark2020

Attempt for TPPmark problem of [the 16th Theorem Proving and Provers meeting (TPP 2020)](https://aabaa.github.io/tpp2020/).

## Explanation

Main program is [TPPmark2020.hs](TPPmark2020.hs).

### 問1.

> 124本のベクトルからなる集合 X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} の各要素を白または黒に塗り分けることを考えます．
> このとき，次の2条件 a), b) を満たすようにベクトルを白または黒に塗り分けることはできないことを証明してください． 
> - a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
> - b) 互いに直交し合う3つのベクトルのうち，少なくとも1本は白色である． 
> 
> Consider painting each element of the set X = {(x,y,z) | x,y,z ∈ {0,±1,±√2}} \ {(0,0,0)} of 124 vectors white or black.
> Prove that the vectors cannot be painted white or black in such a way that the following two conditions a) and b) are met. 
> - a) Whenever two of the vectors are orthogonal, at least one is black. 
> - b) Whenever three of the vectors are mutually orthogonal, at least one is white. 

Xの要素p毎の論理変数 white(p) (真であるときに白、偽であるときに黒であることを表す) と

* ¬white(p1) ∨ ¬white(p2) for p1,p2∈X, p1 and p2 are orthogonal
* white(p1) ∨ white(p2) ∨ white(p3) for p1,p2,p3∈X, p1, p2 and p3 are mutually orthogonal

という制約条件からなる命題論理式をSATソルバを用いて解くことで、そのような塗り分けが可能かどうかを判定することができる。

`solveQ1` が論理式を生成してSATソルバで解く関数であり、 [Q1.cnf](Q1.cnf) が得られた論理式である。
SATソルバは一瞬でUNSATという結果を返すため、そのような塗り分けは不可能なことが示せた。

### 問2. 

> 条件 c) を満たしつつ，条件 a) と b) の少なくとも一方は成り立たないように，ベクトルの集合 X からできるだけ多くの要素を減らしてください． （ヒント: 33本までは減らせることが知られています．）
> - c) 集合内に互いに直交し合う3つのベクトルの集合が少なくとも1つは存在する．
> 
> Reduce as many elements as possible from the set of vectors X such that at least one of the conditions a) and b) does not hold while condition c) is satisfied. (Hint: It is known that you can reduce the number to 33.)
> - c) There is at least one set of three mutually orthogonal vectors in the set. 

まず、 X の各要素pが減らした結果の集合 X'⊆X に含まれるか否かを論理変数 X'(p) によって表すこととする。

次に、条件 a), b), c) は以下のような命題論理式で表すことができる。
* a(X', white) := ∧<sub>(p1,p2) ∈ "orthogonal vectors of X"</sub> (X'(p1) ∧ X'(p2) → ¬white(p1) ∨ ¬white(p2))
* b(X', white) := ∧<sub>(p1,p2,p3)∈"three mutually orthogonal vectors of X"}</sub> (X'(p1) ∧ X'(p2) ∧ X'(p3) → white(p1) ∨ white(p2) ∨ white(p3))
* c(X') := ∨<sub>(p1,p2,p3)∈"three mutually orthogonal vectors of X"</sub> (X'(p1) ∧ X'(p2) ∧ X'(p3))

すると、問題は c(X') ∧ (∀white. ¬a(X', white) ∨ ¬b(X', white)) を満たす X'(p) の割当てのうち、真になっている X'(p) が最小のものを探す問題となる。

また、「33本までは減らせる」ことがヒントとして与えられているので、 基数成約 |X'| ≤ 33 も制約条件に加える。

Totalizer符号化による基数制約の符号化、Tseitin符号化、および冠頭標準形への変換を行ってQDIMACS形式の論理式 [Q2_33.qdimacs](Q2_33.qdimacs) を生成し、QBFソルバ[caqe](https://github.com/ltentrup/caqe/tree/0543174f6c8c624ba37db80d13479c0408d7384e/)を用いて解いたところ、|X'| = 33 である以下の解が得られた。

* (-√2, -1, -1)
* (-√2, -1, 0)
* (-√2, -1, 1)
* (-√2, 0, -√2)
* (-√2, 0, -1)
* (-√2, 0, 0)
* (-√2, 1, -1)
* (-√2, 1, 0)
* (-1, -√2, 0)
* (-1, -1, √2)
* (-1, 0, -√2)
* (-1, 0, 1)
* (-1, 0, √2)
* (-1, 1, -√2)
* (-1, 1, √2)
* (-1, √2, -1)
* (0, -√2, -√2)
* (0, -√2, -1)
* (0, -√2, 1)
* (0, -1, -√2)
* (0, -1, 0)
* (0, -1, 1)
* (0, 0, 1)
* (0, 1, -√2)
* (1, -√2, -1)
* (1, -√2, 0)
* (1, 1, 0)
* (1, 1, √2)
* (1, √2, -1)
* (1, √2, 1)
* (√2, -√2, 0)
* (√2, -1, -1)
* (√2, 0, -1)

次に基数制約を |X'| ≤ 32 に変更した(QDIMACSファイルは[Q2_32.qdimacs](Q2_32.qdimacs))ところ、数時間程度では解を得ることが出来なかった。
そのため、この解が最適解なのか、最適性の証明も反証も出来ていない。

プログラムでは `solveQ2` 関数が該当箇所である。

### 問3.

> より一般的に n 次元 (n > 3) の場合に拡張してください．
> このとき問題は，条件 c') を満たしつつ，条件 a) と b') の少なくとも一方は成り立たないように， n 次元ベクトルの集合を見つけることとなります．
> - a) 2つの直交するベクトルのうち，少なくとも1本は黒色である． 
> - b') 互いに直交し合うn本のベクトルのうち，少なくとも1本は白色である． 
> - c') 集合内に互いに直交し合う n 本のベクトルの集合が少なくとも1つは存在する．
> 
> 一般の場合はとても難しいです．特定の n (> 3) に対して，このようなベクトルの集合を構成する回答も歓迎します．
> 
> More generally, extend it to the case of n dimensions (n > 3). 
> The problem is to find a set of n-dimensional vectors such that at least one of the conditions a) and b') does not hold while condition c') is satisfied.
> - a) Whenever two of the vectors are orthogonal, at least one is black.
> - b') Whenever n vectors are mutually orthogonal, at least one is white.
> - c') There exists at least one set of n vectors in the set that are mutually orthogonal to each other.
> 
> The general case is very difficult. The constitution of such a set of vectors for a particular n (> 3) is also welcome.

n = 4 の場合について、基数制約は加えずに問2と同様のアプローチを試みた(QDIMACSファイルは[Q3_4.qdimacs](Q3_4.qdimacs))が、解を得ることが出来なかった。

プログラム中の `solveQ3` 関数が該当箇所である。
