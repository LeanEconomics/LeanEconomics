% Where does Theorem 1 fail in the life cycle? Scan risk aversion and the rate.
% Reported: d(saving)/dr at a=0 in the top income state, first period of a J-period life,
% and the worst violation of Theorem 1 over ALL stages and reachable wealth.
function lc_bound
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; lam=1/beta-1;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
na=4000; ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
fprintf('lambda = 1/beta-1 = %.4f\n\n  gamma |   r    | dg/dr at (0,zmax) | worst Thm1 violation (all stages)\n',lam);
for gamma=[1 2 3 3.5 4 4.5 5]
  for r=[0.02 0.04 0.0416]
    dr=1e-4; R1=1+r; R2=1+r+dr;
    [c1,g1]=egm_life(R1,beta,gamma,y,Pi,ag,J); [c2,g2]=egm_life(R2,beta,gamma,y,Pi,ag,J);
    dgdr=(g2{J}(1,nz)-g1{J}(1,nz))/dr;
    amax=zeros(J,1);
    for j=0:J-2, k=J-1-j; amax(j+2)=max(interp1(ag,g2{k+1},amax(j+1),'linear','extrap')); end
    worst=0;
    for k=1:J-1
      j=J-1-k; sel=ag<=amax(j+1)+1e-12; if ~any(sel), continue; end
      worst=max(worst,max(max(g1{k+1}(sel,:)-g2{k+1}(sel,:))));
    end
    fprintf(' %6.1f | %.4f | %+17.3f | %.3e%s\n',gamma,r,dgdr,worst/dr,...
      repmat(' <= FAILS',1,worst>1e-9));
  end
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function [c,g]=egm_life(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); g=cell(J,1); c{1}=m; g{1}=zeros(na,nz);
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn; g{k+1}=m-cn;
end
end
