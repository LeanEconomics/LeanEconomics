% Closed-form lower bound on the aggregate floor:
%   v_{k+1}=(Th/R)(1+v_k), u_{k+1}=(1+u_k)/R, d=v-u  =>  d_{k+1} >= (Th-1)/R
%   kappa_k >= 1 - Th/R,  G_k >= 1
%   floor >= (K/(K+1)) * ybar * (1 - Th/R) * (Th-1)/R
% Compare with demand, and with the exact floor, and report the cap the reachable bound needs.
function closedform
beta=0.96; gam=3; J=60; K=J-1; alpha=9/25; delta=2/25; ymax=2.98; ybar=1;
fprintf('    r    | demand  | closed-form floor | exact floor | cf>dem | reach(K+1)\n');
for r=[0.10 0.20 0.50 1.0 2.0 5.0 10.0 20.0]
  R=1+r; Th=(beta*R)^(1/gam); dem=alpha/((1-alpha)*(r+delta));
  cf=(K/(K+1))*ybar*(1-Th/R)*(Th-1)/R;
  x=0; for j=1:K+1, x=R*x+ymax; end
  fprintf(' %7.2f | %7.4f | %17.5f | %11s | %6s | %.3e\n', ...
    r,dem,cf,'-',string(cf>dem),x);
end
fprintf('\n bisect for the smallest r where the closed-form floor beats demand:\n');
lo=0.1; hi=100;
f=@(r) (K/(K+1))*ybar*(1-((beta*(1+r))^(1/gam))/(1+r))*(((beta*(1+r))^(1/gam))-1)/(1+r) ...
       - alpha/((1-alpha)*(r+delta));
for it=1:200, mid=(lo+hi)/2; if f(mid)>0, hi=mid; else lo=mid; end, end
r=hi; R=1+r; x=0; for j=1:K+1, x=R*x+ymax; end
fprintf('   r* = %.4f, demand = %.5f, floor = %.5f, reach(K+1) = %.3e\n', ...
  r,alpha/((1-alpha)*(r+delta)),f(r)+alpha/((1-alpha)*(r+delta)),x);
end
