**Theorem 3.2**
Let $\Omega$ be a measure space and a topological space. Let $\mathbb{P}_{\theta_0}$ be a finite measure on $\Omega$, and $\mu$ be a measure on $\mathbb{R}$.

For any fixed $\theta \neq \theta_0$, all the assumptions hold:
1. The observations are $\mathbf{X}=\left(X_1, \ldots, X_n\right)$, where the $X_i$ are i.i.d. with probability density $f\left(x_i \mid \theta\right)$ with respect to $\mathbb{P}_{\theta_0}$ <font color="LightCoral">(?)</font>.
2. For $x\in \mathbb{R}$, $\neg \left(E_{\theta_0} \left[\frac{f(x|\theta)}{f(x|\theta_0)}\right] \rightarrow \text{constant}\right)$ $\mu$-a.e.
3. For any random variable $X: \Omega \rightarrow \mathbb{R}$, support of $f_\theta$ is equal to support of $f_{\theta_0}$.
Then we have
$$P_{\theta_0}\left(L\left(\theta_0 \mid \mathbf{X}\right)>L(\theta \mid \mathbf{X})\right) \rightarrow 1 \text { as } n \rightarrow \infty.$$

Proof.

The inequality is equivalent to

$$
\frac{1}{n} \Sigma \log \left[f\left(X_i \mid \theta\right) / f\left(X_i \mid \theta_0\right)\right]<0 .
$$


By the law of large numbers, the left side tends in probability toward

$$
E_{\theta_0} \log \left[f(X \mid \theta) / f\left(X \mid \theta_0\right)\right] .
$$


Since $-\log$ is strictly convex, Jensen's inequality shows that

$$
E_{\theta_0} \log \left[f(X \mid \theta) / f\left(X \mid \theta_0\right)\right]<\log E_{\theta_0}\left[f(X \mid \theta) / f\left(X \mid \theta_0\right)\right]=0
$$

and the result follows.