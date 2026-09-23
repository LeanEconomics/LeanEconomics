% Is the apparent Theorem 1 failure at gamma=5 real, or interpolation error?
% Refine the grid and watch the magnitude of the violation.
function lc_robust(gamma)
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
r1=0.040; r2=0.041; R1=1+r1; R2=1+r2; dr=r2-r1;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
fprintf('\n==== gamma=%g : grid refinement (violation of g1<=g2, and of gap<=dr*a)\n',gamma);
for na=[2000 4000 8000 16000]
  ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
  [c1,g1]=egm_life(R1,beta,gamma,y,Pi,ag,J); [c2,g2]=egm_life(R2,beta,gamma,y,Pi,ag,J);
  amax=zeros(J,1);
  for j=0:J-2, k=J-1-j; amax(j+2)=max(interp1(ag,g2{k+1},amax(j+1),'linear','extrap')); end
  worstT1=0; worstGap=0; kT1=0; aT1=0; zT1=0;
  for k=1:J-1
    j=J-1-k; A=amax(j+1); sel=ag<=A+1e-12; if ~any(sel), continue; end
    D1=g1{k+1}(sel,:)-g2{k+1}(sel,:);            % >0 violates Theorem 1
    [v,ix]=max(D1(:)); if v>worstT1, worstT1=v; [ia,iz]=ind2sub(size(D1),ix);
      kT1=k; as=ag(sel); aT1=as(ia); zT1=iz; end
    G=(c2{k+1}(sel,:)-c1{k+1}(sel,:))/dr-ag(sel); worstGap=max(worstGap,max(G(:)));
  end
  fprintf('  na=%5d: max(g1-g2)=%.3e at stage %d, a=%.3f, z=%d | max(gap-dr*a)/dr=%.3e\n',...
    na,worstT1,kT1,aT1,zT1,worstGap);
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
