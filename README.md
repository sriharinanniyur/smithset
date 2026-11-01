# Autoformalization of Smith set algorithm

[AI@70 hackathon](https://ai.dartmouth.edu/ai-70-events/what-must-remain-human-conference/ai-70-student-hackathon) project. Formal verification of an algorithm to compute the Smith set in an election. Lean specification and proof by Fable 5.1.

### 4th place winner!

A few post-hackathon notes:
- As detailed in the demo, we assume ties are suitably broken before the main computation. The literature often does this by just saying "assume an odd number of voters."
- The stopping condition $\sum_{c_i \in S} \text{score}(c_i) = \binom{|S|}{2} + |S|(n - |S|)$ (provided we add elements to $S$ in descending order of score) is a special case of [Landau's theorem](https://arxiv.org/pdf/1509.04205).
    - Note one can also write it as $\sum_{c_i \not \in S} \text{score}(c_i) = \binom{n - |S|}{2}$.
- Candidates are enumerated in the simplest way, as elements of $\mathbb{Z}_n$. This may not be immediately obvious from the code.
