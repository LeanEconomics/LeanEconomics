% A state-dependent lower bound on consumption, with human wealth accumulated by the
% RISK-ADJUSTED (power-mean) expectation and CAPPED where the borrowing constraint could bind.
%   kappa_0 = 1, kappa_{k+1} = kappa_k R/(Thorn + kappa_k R)      (the LifeCycle recursion)
%   H_0 = 0,  H_{k+1}(z) = min( M^z_{-g}(y_w + H_k(w))/R , (1/kappa_{k+1} - 1) y_z )
% Claim:  kappa_k (m + H_k(z)) <= c_k(a,z).
function incidence
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; R=1.04; gam=3;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1;                       % kap(k+1) = kappa_k
for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); Hmin=zeros(J,1); Hpm=zeros(nz,J);  % Hmin = the old min-income human wealth
for k=1:J-1
  x=y+H(:,k);                                    % y_w + H_k(w)
  pm=(Pi*(x.^(-gam))).^(-1/gam);                 % power mean by row
  Hpm(:,k+1)=pm/R;
  cap=(1./kap(k+1)-1).*y;
  H(:,k+1)=min(pm/R,cap);
  Hmin(k+1)=(min(y)+Hmin(k))/R;
end
fprintf('gamma=%g  kappa_59=%.5f  Thorn=%.6f\n',gam,kap(J),Th);
fprintf('\n  z |   y_z |  H_59(z) | uncapped |  cap   | old H_min | binding?\n');
for z=1:nz
  cap=(1/kap(J)-1)*y(z);
  fprintf(' %2d | %5.2f | %8.3f | %8.3f | %6.2f | %9.3f | %s\n',z,y(z),H(z,J),Hpm(z,J),cap,Hmin(J),...
    ternary(H(z,J)<Hpm(z,J)-1e-9,'CAPPED','free'));
end
% compare with the truth
ag=[0; exp(linspace(log(1e-4),log(600),2499))'];
c=egm(R,beta,gam,y,Pi,ag,J);
fprintf('\n bound vs truth at stage 59 (first period of life):\n');
fprintf('    a  | z |  new bound | old bound | true c | new/true | old/true\n');
for a=[0 1 5]
  ia=find(ag>=a,1);
  for z=[1 4 7]
    m=y(z)+R*ag(ia); nb=kap(J)*(m+H(z,J)); ob=kap(J)*(m+Hmin(J)); tc=c{J}(ia,z);
    fprintf(' %5.2f | %d | %10.4f | %9.4f | %6.4f | %8.3f | %8.3f\n',ag(ia),z,nb,ob,tc,nb/tc,ob/tc);
  end
end
% and the check that the bound never exceeds the truth anywhere
worst=0; wz=0; wa=0;
for z=1:nz
  m=y(z)+R*ag; b=kap(J)*(m+H(z,J)); r=b./c{J}(:,z);
  [v,i]=max(r); if v>worst, worst=v; wz=z; wa=ag(i); end
end
fprintf('\n max over the whole grid of (bound/truth) at stage 59: %.4f at a=%.2f, z=%d\n',worst,wa,wz);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function s=ternary(c,a,b), if c, s=a; else s=b; end, end
function c=egm(R,beta,gamma,y,Pi,ag,J)
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
