% Critical relative risk aversion: the largest gamma at which Theorem 1 survives the whole
% life cycle, by bisection, at several interest rates and horizons.
function lc_crit
beta=0.96; rho=0.9; sigma=0.4; nz=7;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
na=3000; ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
fprintf('  J  |   r    | critical gamma (Theorem 1 holds below it)\n');
for J=[20 40 60]
  for r=[0.02 0.04 0.0416]
    lo=1; hi=6;
    for it=1:22
      mid=(lo+hi)/2;
      if viol(mid,r,beta,y,Pi,ag,J)>1e-9, hi=mid; else lo=mid; end
    end
    fprintf(' %3d | %.4f | %.3f\n',J,r,lo);
  end
end
end
function w=viol(gamma,r,beta,y,Pi,ag,J)
dr=1e-4; [c1,g1]=egm_life(1+r,beta,gamma,y,Pi,ag,J); [c2,g2]=egm_life(1+r+dr,beta,gamma,y,Pi,ag,J);
nz=numel(y); amax=zeros(J,1);
for j=0:J-2, k=J-1-j; amax(j+2)=max(interp1(ag,g2{k+1},amax(j+1),'linear','extrap')); end
w=0;
for k=1:J-1
  j=J-1-k; sel=ag<=amax(j+1)+1e-12; if ~any(sel), continue; end
  w=max(w,max(max(g1{k+1}(sel,:)-g2{k+1}(sel,:))));
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
