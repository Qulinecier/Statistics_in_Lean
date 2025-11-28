**Theorem 3.2** 

Under assumptions

(A0) The distributions $P_\theta$ of the observations are distinct (otherwise, $\theta$ cannot be estimated consistently ${ }^2$ ).
(A1) The distributions $P_\theta$ have common support.
(A2) The observations are $\mathbf{X}=\left(X_1, \ldots, X_n\right)$, where the $X_i$ are iid with probability density $f\left(x_i \mid \theta\right)$ with respect to $\mu$,

$$
P_{\theta_0}\left(L\left(\theta_0 \mid \mathbf{X}\right)>L(\theta \mid \mathbf{X})\right) \rightarrow 1 \text { as } n \rightarrow \infty
$$

for any fixed $\theta \neq \theta_0$.

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

**Theorem 3.7**
Let $X_1, \ldots, X_n$ satisfy 

(A0) The distributions $P_\theta$ of the observations are distinct (otherwise, $\theta$ cannot be estimated consistently ${ }^2$ ).
(A1) The distributions $P_\theta$ have common support.
(A2) The observations are $\mathbf{X}=\left(X_1, \ldots, X_n\right)$, where the $X_i$ are iid with probability density $f\left(x_i \mid \theta\right)$ with respect to $\mu$.
(A3) The parameter space $\Omega$ contains an open set $\omega$ of which the true parameter value $\theta_0$ is an interior point.
and suppose that for almost all $x, f(x \mid \theta)$ is differentiable with respect to $\theta$ in $\omega$, with derivative $f^{\prime}(x \mid \theta)$. Then, with probability tending to 1 as $n \rightarrow \infty$, the likelihood equation
$$\frac{\partial}{\partial \theta} l(\theta \mid \mathbf{x})=0$$

or, equivalently, the equation
$$l^{\prime}(\theta \mid \mathbf{x})=\Sigma \frac{f^{\prime}\left(x_i \mid \theta\right)}{f\left(x_i \mid \theta\right)}=0$$

has a root $\hat{\theta}_n=\hat{\theta}_n\left(x_1, \ldots, x_n\right)$ such that $\hat{\theta}_n\left(X_1, \ldots, X_n\right)$ tends to the true value $\theta_0$ in probability.



Proof.

Let $a$ be small enough so that $\left(\theta_0-a, \theta_0+a\right) \subset \omega$, and let

$$
S_n=\left\{\mathbf{x}: l\left(\theta_0 \mid \mathbf{x}\right)>l\left(\theta_0-a \mid \mathbf{x}\right) \quad \text { and } \quad l\left(\theta_0 \mid \mathbf{x}\right)>l\left(\theta_0+a \mid \mathbf{x}\right)\right\} .
$$


By Theorem 3.2, $P_{\theta_0}\left(S_n\right) \rightarrow 1$. For any $\mathbf{x} \in S_n$, there thus exists a value $\theta_0-a< \hat{\theta}_n<\theta_0+a$ at which $l(\theta)$ has a local maximum, so that $l^{\prime}\left(\hat{\theta}_n\right)=0$. Hence, for any $a>0$ sufficiently small, there exists a sequence $\hat{\theta}_n=\hat{\theta}_n(a)$ of roots such that

$$
P_{\theta_0}\left(\left|\hat{\theta}_n-\theta_0\right|<a\right) \rightarrow 1
$$


It remains to show that we can determine such a sequence, which does not depend on $a$.

Let $\theta_n^*$ be the root closest to $\theta_0$. [This exists because the limit of a sequence of roots is again a root by the continuity of $l(\theta)$.] Then, clearly, $P_{\theta_0}\left(\left|\theta_n^*-\theta_0\right|<a\right) \rightarrow 1$ and this completes the proof.