# usage: calibrate.py <floor> ; applies SEALED_RULE.txt to the floor and to the tau of readings 001 and 002.
import sys, math
floor = int(sys.argv[1])
lam_bar = 3.8615926744e-13   # reduced Compton wavelength, m (CODATA 2022), u_r 3.0e-10
c = 299792458.0              # m/s, exact
t_C = lam_bar / c            # s
s_hb = t_C / floor
print(f"floor = {floor} heartbeats = one Compton time t_C = {t_C:.10e} s")
print(f"one heartbeat = {s_hb:.6e} s")
taus = {("001","M2"):35.50e-9, ("001","M2 Ultra"):33.95e-9, ("002","M2"):38.80e-9, ("002","M2 Ultra"):35.64e-9}
for (exp, m), tau in taus.items():
    G = tau / s_hb
    print(f"{exp} {m:9s} tau = {tau*1e9:.2f} ns/hb  Gamma = {G:.4e}  rapidity = {math.acosh(G):.4f}")
eta = math.log(19 + 2*math.sqrt(90))
print(f"step rapidity eta = ln(19 + 2 sqrt 90) = {eta:.6f}")
print(f"horizon distance = lam_bar / eta = {lam_bar/eta:.6e} m = {1/eta:.6f} reduced Compton wavelengths")
print(f"acceleration a = c eta / t_C = {c*eta/t_C:.6e} m/s^2")
