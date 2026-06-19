# Minimizing Variations

Source: `instrument/chapters/06.tex:714`
Environment: `phenomenon`
Original title: `Minimizing Variations~\cite{courant1953}`

## Description

**Note.** For a comprehensive treatment of the calculus of variations, see Brenner and Scott~\cite{brenner2008}
and Courant and Hilbert~\cite{courant1953}.


We consider the functional
\[
J[x] = \int_a^b f\bigl(t,x(t),\dot{x}(t)\bigr)\, dt,
\]
where $x$ is a twice continuously differentiable function with fixed
endpoints $x(a)=x_a$ and $x(b)=x_b$. Let $\eta(t)$ be an admissible
perturbation with $\eta(a)=\eta(b)=0$, and define the variation
\[
x_\varepsilon(t) = x(t) + \varepsilon\,\eta(t), \qquad \varepsilon\in\mathbb{R}.
\]
The directional derivative of $J$ at $x$ in the direction $\eta$ is
\[
\delta J[x;\eta]
  = \left.\frac{d}{d\varepsilon} J[x_\varepsilon]\right|_{\varepsilon=0}
  = \left.\frac{d}{d\varepsilon}
       \int_a^b f\bigl(t, x_\varepsilon(t), \dot{x}_\varepsilon(t)\bigr)\, dt
    \right|_{\varepsilon=0}.
\]
Since the integration limits do not depend on $\varepsilon$, the
derivative may be moved inside:
\[
\delta J[x;\eta]
  = \int_a^b
      \left.\frac{\partial}{\partial\varepsilon}
      f\bigl(t, x_\varepsilon(t), \dot{x}_\varepsilon(t)\bigr)
      \right|_{\varepsilon=0} dt.
\]
By the chain rule,
\[
\frac{\partial}{\partial\varepsilon}
 f\bigl(t, x_\varepsilon(t), \dot{x}_\varepsilon(t)\bigr)
 = f_x(t,x(t),\dot{x}(t))\,\eta(t)
 + f_{\dot{x}}(t,x(t),\dot{x}(t))\,\dot{\eta}(t).
\]
Thus
\[
\delta J[x;\eta]
  = \int_a^b \Bigl(
      f_x(t,x,\dot{x})\,\eta(t)
      + f_{\dot{x}}(t,x,\dot{x})\,\dot{\eta}(t)
    \Bigr)\, dt.
\]
Integrate the second term by parts:
\[
\int_a^b f_{\dot{x}}\,\dot{\eta}\, dt
  = \bigl[f_{\dot{x}}\eta\bigr]_{a}^{b}
    - \int_a^b \frac{d}{dt}\bigl(f_{\dot{x}}\bigr)\,\eta(t)\, dt.
\]
Because $\eta(a)=\eta(b)=0$, the boundary term vanishes. Therefore
\[
\delta J[x;\eta]
  = \int_a^b
       \left(
         f_x - \frac{d}{dt} f_{\dot{x}}
       \right)\eta(t)\, dt.
\]
If $x$ is a stationary point of $J$, then $\delta J[x;\eta]=0$ for all
admissible $\eta$. The fundamental lemma of the calculus of variations
implies
\[
f_x(t,x,\dot{x}) - \frac{d}{dt}f_{\dot{x}}(t,x,\dot{x}) = 0,
\]
for all $t\in(a,b)$. This is the Euler--Lagrange equation, more commonly
represented as
\begin{equation}
\frac{\partial f}{\partial x} = \frac{d}{dt}\frac{\partial f}{\partial\dot{x}}.
\end{equation}

This derivation demonstrates that the Euler--Lagrange equation selects the
trajectory with no first-order change under admissible perturbations. No
hidden motion can be inserted without altering the notebook. The path is
stationary in its informational curvature.
