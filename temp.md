
For any fixed $\theta \neq \theta_0$, all the assumptions hold:
1. The observations are $\mathbf{X}=\left(X_1, \ldots, X_n\right)$, where the $X_i$ are i.i.d. with probability density $f\left(x_i \mid \theta\right)$ with respect to $\mu$.
2. $\frac{f(X (\omega)| \theta)}{f(X(\omega)| \theta|_0)}$ is not a.s. constant under $P_{\theta_0}$.
3. For any random variable $X: \Omega \rightarrow \mathbb{R}$, support of $f_\theta$ is equal to support of $f_{\theta_0}$.


**Theorem 3.2**

Under assumptions (A0)-(A2),

$$
P_{\theta_0}\left(L\left(\theta_0 \mid \mathbf{X}\right)>L(\theta \mid \mathbf{X})\right) \rightarrow 1 \quad \text { as } n \rightarrow \infty
$$

for any fixed $\theta \neq \theta_0$.

*Proof.*

The likelihood is defined as
$$L(\theta| \mathbf{X}(\omega)) = \prod^n_{i=1}f(X_i(\omega) | \theta).$$
We are given i.i.d. random variables
$$X_1, X_2, \ldots, X_n:\left(\Omega, \mathcal{F}, P_{\theta_0}\right) \longrightarrow \mathbb{R},$$
where the distribution of each $X_i$ under parameter $\theta$ has density $f(x | \theta)$ w.r.t. measure $\mu$.

$$\begin{aligned}
&~\quad \left\{L\left(\theta_0 \mid \mathbf{X}(\omega)\right)>L(\theta \mid \mathbf{X}(\omega))\right\}\\
&= \left\{\frac{L(\theta \mid \mathbf{X}(\omega))}{L\left(\theta_0 \mid \mathbf{X}(\omega)\right)}< 1\right\}\\
&= \left\{\frac{\prod^n_{i=1}f(X_i(\omega) | \theta)}{\prod^n_{i=1}f(X_i(\omega) | \theta_0)}<1\right\}\\
&= \left\{\log\left(\frac{\prod^n_{i=1}f(X_i(\omega) | \theta)}{\prod^n_{i=1}f(X_i(\omega) | \theta_0)}\right)<0\right\}\\
&= \left\{\log\left(\prod^n_{i=1}\frac{f(X_i(\omega) | \theta)}{f(X_i(\omega) | \theta_0)}\right)<0\right\}\\
&= \left\{\sum\limits^n_{i=1}\log\left(\frac{f(X_i(\omega) | \theta)}{f(X_i(\omega) | \theta_0)}\right)<0\right\}\\
&= \left\{\frac{1}{n}\sum\limits^n_{i=1}\log\left(\frac{f(X_i(\omega) | \theta)}{f(X_i(\omega) | \theta_0)}\right)<0\right\}
\end{aligned}$$
Then our goal is now
$$P_{\theta_0}\left(\left\{\omega \in \Omega : \frac{1}{n}\sum\limits^n_{i=1}\log\left(\frac{f(X_i(\omega) | \theta)}{f(X_i(\omega) | \theta_0)}\right)<0\right\}\right) \rightarrow 1 \quad \text { as } n \rightarrow \infty.$$


By the law of large number, we have

$$\small \forall \varepsilon>0, \quad P_{\theta_0}\left(\left\{ \omega \in \Omega : \left|\frac{1}{n} \sum_{i=1}^n \log \left(\frac{f\left(X_i(\omega) \mid \theta\right)}{f\left(X_i(\omega) \mid \theta_0\right)}\right)-\mathbb{E}_{\theta_0} \log \left(\frac{f(X(\omega) \mid \theta)}{f\left(X(\omega) \mid \theta_0\right)}\right)\right|>\varepsilon\right\}\right) \longrightarrow 0$$
that is
$$\small \forall \varepsilon>0, \quad P_{\theta_0}\left(\left\{ \omega \in \Omega : \left|\frac{1}{n} \sum_{i=1}^n \log \left(\frac{f\left(X_i(\omega) \mid \theta\right)}{f\left(X_i(\omega) \mid \theta_0\right)}\right)-\mathbb{E}_{\theta_0} \log \left(\frac{f(X(\omega) \mid \theta)}{f\left(X(\omega) \mid \theta_0\right)}\right)\right|<\varepsilon\right\}\right) \longrightarrow 1$$

Let $$\varepsilon :=  -\mathbb{E}_{\theta_0} \log \left(\frac{f(X(\omega) \mid \theta)}{f\left(X(\omega) \mid \theta_0\right)}\right) . \tag{1}$$

The proof of $\varepsilon >0$ is shown later.

Then 

$$\tiny \left\{ \omega \in \Omega : \left|\frac{1}{n} \sum_{i=1}^n \log \left(\frac{f\left(X_i(\omega) \mid \theta\right)}{f\left(X_i(\omega) \mid \theta_0\right)}\right)-\mathbb{E}_{\theta_0} \log \left(\frac{f(X(\omega) \mid \theta)}{f\left(X(\omega) \mid \theta_0\right)}\right)\right|>\varepsilon\right\} \subseteq \left\{ \omega \in  \Omega : \frac{1}{n} \sum_{i=1}^n \log \left(\frac{f\left(X_i(\omega) \mid \theta\right)}{f\left(X_i(\omega) \mid \theta_0\right)}\right) < 0\right\} \subseteq \Omega$$

Hence by using Sandwich theorem (as $P_{\theta_0} (\Omega) \rightarrow 1$), we finish the proof.

Finally, we need to show (1) by using Jensen's inequality, 
We need that $\frac{f(X (\omega)| \theta)}{f(X(\omega)| \theta|_0)}$ is not a.s. constant under $P_{\theta_0}$.
Hence $$E_{\theta_0} \log \left[f(X \mid \theta) / f\left(X \mid \theta_0\right)\right]<\log E_{\theta_0}\left[f(X \mid \theta) / f\left(X \mid \theta_0\right)\right]=0.$$
