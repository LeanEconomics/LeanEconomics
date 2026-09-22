% Certainty-equivalent benchmark in closed form: with an interior solution the deterministic
% life-cycle household has c_t = c_0 (beta R)^{t/gamma} and c_0 = W(R)/D(R).
function precaut2
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
fprintf('  gamma | det saving g0 | d g0/dr (certainty equiv) | stoch d g/dr | min assets on det path\n');
for gam=[1 3 5 8]
  [g0,amin]=detg(1.04,beta,gam,ypath);
  gp=detg(1.04+1e-6,beta,gam,ypath); dg=(gp-g0)/1e-6;
  fprintf(' %6.1f | %13.6f | %25.3f | %12s | %10.4f\n',gam,g0,dg,'see below',amin);
end
fprintf('\nstochastic d(saving)/dr at (a=0,z_max), from the solved model:\n');
ag=[0; exp(linspace(log(1e-4),log(600),3999))'];
for gam=[1 3 5 8]
  g=zeros(1,2); i=0;
  for r=[0.040 0.041]
    i=i+1; c=egm_life(1+r,beta,gam,y,Pi,ag,J); g(i)=y(nz)-c{J}(1,nz);
  end
  fprintf('  gamma=%4.1f : g=%9.6f, d/dr = %+9.3f\n',gam,g(1),(g(2)-g(1))/0.001);
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function [g0,amin]=detg(R,beta,gam,ypath)
J=numel(ypath); t=(0:J-1)';
W=sum(ypath.*R.^(-t)); D=sum(beta.^(t/gam).*R.^(t/gam-t));
c0=W/D; c=c0*(beta*R).^(t/gam);
a=zeros(J+1,1); for k=1:J, a(k+1)=R*a(k)+ypath(k)-c(k); end
amin=min(a(2:J)); g0=ypath(1)-c0;
end
function c=egm_life(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
end
end
