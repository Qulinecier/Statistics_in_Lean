<b>Theorem 3.10</b>

Let $X_1, \ldots, X_n$ be iid, each with density $f(x \mid \theta)$ with respect to a $\sigma$-finite measure $\mu$, where $\theta$ is real-valued, and suppose the following regularity conditions hold.
(a) The parameter space $\Omega$ is an open interval (not necessarily finite).
(b) The distributions $P_\theta$ of the $X_i$ have common support, so that the set $A=\{x$ : $f(x \mid \theta)>0\}$ is independent of $\theta$.
(c) For every $x \in A$, the density $f(x \mid \theta)$ is third differentiable with respect to $\theta$, and the third derivative is continuous in $\theta$.
(d) The integral $\int f(x \mid \theta) d \mu(x)$ can be third differentiated under the integral sign.
(e) The Fisher information $I(\theta)$ defined by (3.5.10) satisfies $0<I(\theta)<\infty$.
(f) For any given $\theta_0 \in \Omega$, there exists a positive number $c$ and a function $M(x)$ (both of which may depend on $\theta_0$ ) such that
$$\left|\frac{\partial^3}{\partial \theta^3} \log f(x \mid \theta)\right| \leq M(x)$$
for all $x \in A, \quad \theta_0-c<\theta<\theta_0+c$ with
$$E_{\theta_0}[M(\mathbf{X})]<\infty.$$

Then, any consistent sequence $\hat{\theta}_n=\hat{\theta}_n\left(X_1, \ldots, X_n\right)$ of roots of the likelihood equation satisfies
$$\sqrt{n}\left(\hat{\theta}_n-\theta\right) \xrightarrow{£} N\left(0, \frac{1}{I(\theta)}\right) .$$

We shall call such a sequence $\hat{\theta}_n$ an efficient likelihood estimator (ELE) of $\theta$. It is typically (but need not be, see Example 4.1) provided by the MLE. Note also that any sequence $\hat{\theta}_n^*$ satisfying (3.19) is asymptotically efficient in the sense of Definition 2.4.

*Proof of Theorem 3.10.* 
For any fixed $\mathbf{x}$, expand $l^{\prime}\left(\hat{\theta}_n\right)$ about $\theta_0$,
$$l^{\prime}\left(\hat{\theta}_n\right)=l^{\prime}\left(\theta_0\right)+\left(\hat{\theta}_n-\theta_0\right) l^{\prime \prime}\left(\theta_0\right)+\frac{1}{2}\left(\hat{\theta}_n-\theta_0\right)^2 l^{\prime \prime \prime}\left(\theta_n^*\right)$$
where $\theta_n^*$ lies between $\theta_0$ and $\hat{\theta}_n$
By assumption, the left side is zero, so that
$$\sqrt{n}\left(\hat{\theta}_n-\theta_0\right)=\frac{(1 / \sqrt{n}) l^{\prime}\left(\theta_0\right)}{-(1 / n) l^{\prime \prime}\left(\theta_0\right)-(1 / 2 n)\left(\hat{\theta}_n-\theta_0\right) l^{\prime \prime \prime}\left(\theta_n^*\right)}$$

where it should be remembered that $l(\theta), l^{\prime}(\theta)$, and so on are functions of $\mathbf{X}$ as well as $\theta$. We shall show that

$$
\frac{1}{\sqrt{n}} l^{\prime}\left(\theta_0\right) \xrightarrow{\mathcal{L}} N\left[0, I\left(\theta_0\right)\right],
$$

that

$$
-\frac{1}{n} l^{\prime \prime}\left(\theta_0\right) \xrightarrow{P} I\left(\theta_0\right)
$$

and that

$$
\frac{1}{n} l^{\prime \prime \prime}\left(\theta_n^*\right) \quad \text { is bounded in probability. }
$$


The desired result then follows from Theorem 1.8.10.
Of the above statements, (3.18) follows from the fact that

$$
\frac{1}{\sqrt{n}} l^{\prime}\left(\theta_0\right)=\sqrt{n} \frac{1}{n} \sum\left[\frac{f^{\prime}\left(X_i \mid \theta_0\right)}{f\left(X_i \mid \theta_0\right)}-E_{\theta_0} \frac{f^{\prime}\left(X_i \mid \theta_0\right)}{f\left(X_i \mid \theta_0\right)}\right]
$$

since the expectation term is zero, and then from the central limit theorem (CLT) and the definition of $I(\theta)$.

Next, (3.19) follows because

$$
-\frac{1}{n} l^{\prime \prime}\left(\theta_0\right)=\frac{1}{n} \sum \frac{f^{\prime 2}\left(X_i \mid \theta_0\right)-f\left(X_i \mid \theta_0\right) f^{\prime \prime}\left(X_i \mid \theta_0\right)}{f^2\left(X_i \mid \theta_0\right)},
$$

and, by the law of large numbers, this tends in probability to

$$
I\left(\theta_0\right)-E_{\theta_0} \frac{f^{\prime \prime}\left(X_i \mid \theta_0\right)}{f\left(X_i \mid \theta_0\right)}=I\left(\theta_0\right) .
$$


Finally, (3.20) is established by noting

$$
\frac{1}{n} l^{\prime \prime \prime}(\theta)=\frac{1}{n} \sum \frac{\partial^3}{\partial \theta^3} \log f\left(X_i \mid \theta\right)
$$

so that by (3.15),

$$
\left|\frac{1}{n} l^{\prime \prime \prime}\left(\theta_n^*\right)\right|<\frac{1}{n}\left[M\left(X_1\right)+\cdots+M\left(X_n\right)\right]
$$

with probability tending to 1 . The right side tends in probability to $E_{\theta_0}[M(X)]$, and this completes the proof.
