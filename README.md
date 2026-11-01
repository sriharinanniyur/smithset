# Autoformalization of Smith set algorithm

AI@70 hackathon project. Formal verification of an algorithm to compute the Smith set in an election. Lean specification and proof by Fable 5.1.

### 4th place winner!

A few post-hackathon notes:
- We assume ties are suitably broken before the main computation. The literature often does this by just saying "assume an odd number of voters."
- The stopping condition $\sum_{c_i \in S} \text{score}(c_i) = \binom{|S|}{2} + |S|(n - |S|)$ is a special case of [Landau's theorem](https://arxiv.org/pdf/1509.04205).
    - Note one can also write it as $\sum_{c_i \not \in S} \text{score}(c_i) = \binom{n - |S|}{2}$.
