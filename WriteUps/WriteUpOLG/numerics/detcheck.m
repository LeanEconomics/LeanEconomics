% Deterministic life cycle: closed form, the duration criterion, and the threshold.
%  c_k(a) = kap_k (y + R a + H_k),  1/kap_k = sum_{i<=k} q^i,  q = (beta R)^{1/gam}/R
%  H_0 = 0, H_{k+1} = (y + H_k)/R
% Theorem 1 at a = 0 holds iff d/dR of kap_K (y + H_K) <= 0, i.e. T_y >= (1 - 1/gam) T_c.
function detcheck
beta=0.96; J=60; K=J-1; y=1;
fprintf('   r    | gamma* (saving stops rising with R at a=0) | T_y   | T_c   | (1-1/g*)T_c\n');
for r=[0.00 0.02 0.04 0.06]
  g=bisect(@(gam) crit(gam,r,beta,K,y),0.2,20);
  [~,Ty,Tc]=crit(g,r,beta,K,y);
  fprintf(' %+.3f | %42.4f | %5.2f | %5.2f | %11.2f\n',r,g,Ty,Tc,(1-1/g)*Tc);
end
fprintf('\n check at r=0.04: saving at a=0 vs R, for gamma below and above the threshold\n');
r=0.04; D=1e-4;
for gam=[1 2 3 4 4.33 4.5 5]
  s1=sav(1+r,beta,gam,K,y,0); s2=sav(1+r+D,beta,gam,K,y,0);
  s1a=sav(1+r,beta,gam,K,y,5); s2a=sav(1+r+D,beta,gam,K,y,5);
  fprintf('   gamma=%5.2f : ds/dR at a=0  %+.4e ; at a=5  %+.4e\n',gam,(s2-s1)/D,(s2a-s1a)/D);
end
end
function [v,Ty,Tc]=crit(gam,r,beta,K,y)
R=1+r; q=(beta*R)^(1/gam)/R;
i=(0:K)'; Dc=sum(q.^i); Tc=sum(i.*q.^i)/Dc;
w=y*R.^(-i); Ty=sum(i.*w)/sum(w);
v=Ty-(1-1/gam)*Tc;      % >0 means Theorem 1 holds at a=0
end
function s=sav(R,beta,gam,K,y,a)
q=(beta*R)^(1/gam)/R; i=(0:K)'; kap=1/sum(q.^i);
H=0; for j=1:K, H=(y+H)/R; end
s=(y+R*a)-kap*(y+R*a+H);
end
function x=bisect(f,lo,hi)
for it=1:200, m=(lo+hi)/2; if f(m)>0, lo=m; else hi=m; end, end
x=lo;
end
