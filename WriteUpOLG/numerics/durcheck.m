% In the certainty-equivalent life cycle, c0 = W(R)/D(R) with
%   W = sum_t y_t R^-t                    (human wealth)
%   D = sum_t beta^{t/g} R^{t/g - t}      (the price of the optimal consumption path)
% so  dlog c0 / dlog R = -T_y + (1 - 1/g) T_c,  T_y, T_c the durations of the two streams.
% Theorem 1 at zero wealth  <=>  T_y > (1 - 1/g) T_c.  Check it against the exact derivative.
function durcheck
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; R=1.04;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D0]=eig(Pi'); [~,k]=max(abs(diag(D0))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
t=(0:J-1)';
W=sum(ypath.*R.^(-t)); Ty=sum(t.*ypath.*R.^(-t))/W;
fprintf('income duration T_y = %.3f  (J=%d, R=%.2f, path from z_max)\n',Ty,J,R);
fprintf('\n  gamma |   T_c   | (1-1/g) T_c |  T_y  | predicted | exact dlog c0/dlog R | Thm 1 at a=0\n');
for gam=[1 2 3 3.5 4 4.5 5 8]
  w=beta.^(t/gam).*R.^(t/gam-t); D=sum(w); Tc=sum(t.*w)/D;
  pred=-Ty+(1-1/gam)*Tc;
  c0=W/D; dR=1e-7; Wp=sum(ypath.*(R+dR).^(-t)); Dp=sum(beta.^(t/gam).*(R+dR).^(t/gam-t));
  exact=((Wp/Dp-c0)/dR)*(R/c0);
  fprintf(' %6.1f | %7.3f | %11.3f | %5.2f | %+9.3f | %+20.3f | %s\n',gam,Tc,(1-1/gam)*Tc,Ty,pred,exact,...
    ternary(pred<0,'holds','FAILS'));
end
% critical gamma in the certainty-equivalent problem
lo=1; hi=20;
for i=1:60
  g=(lo+hi)/2; w=beta.^(t/g).*R.^(t/g-t); Tc=sum(t.*w)/sum(w);
  if -Ty+(1-1/g)*Tc < 0, lo=g; else hi=g; end
end
fprintf('\ncritical gamma (certainty equivalent, this income path): %.3f\n',lo);
fprintf('critical gamma (stochastic, measured earlier): 3.391\n');
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function s=ternary(c,a,b), if c, s=a; else s=b; end, end
