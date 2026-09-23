% Where does the provable floor lose against the truth at the top of the interval?
% (i) consumption: truth vs the upper bound kap_k(m+H_k) that drives the floor
% (ii) the asset path: provable floor B_j vs the cohort's true mean assets
% (iii) counterfactual: run the floor recursion with the TRUE mean consumption instead
function diag
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; r=0.08; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz); R=1+r;
kap=zeros(J,1); kap(1)=1; Th=(beta*R)^(1/gam);
for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
na=1200; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
% simulate the cohort
mu=zeros(na,nz); mu(1,:)=nu'; A=zeros(J,1); C=zeros(J,1); Cb=zeros(J,1);
for j=0:J-1
  k=J-1-j; w=sum(mu,2);
  A(j+1)=w'*ag;
  C(j+1)=sum(sum(mu.*c{k+1}));
  Cb(j+1)=sum(sum(mu.*(kap(k+1)*(m+repmat(H(:,k+1)',na,1)))));
  if j==J-1, break; end
  ap=m-c{k+1}; new=zeros(na,nz);
  for z=1:nz
    ww=mu(:,z); idx=ww>1e-16; if ~any(idx), continue; end
    x=min(max(ap(:,z),ag(1)),ag(end)); [~,bin]=histc(x,ag); bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    for i=find(idx)'
      b=bin(i); f=frac(i);
      new(b,:)=new(b,:)+ww(i)*(1-f)*Pi(z,:); new(b+1,:)=new(b+1,:)+ww(i)*f*Pi(z,:);
    end
  end
  mu=new;
end
% provable asset floor path (scalar, with clamp)
hb=zeros(J,1); for k=1:J, hb(k)=nu'*H(:,k); end
B=zeros(J,1);
for j=1:J-1
  k=J-1-(j-1); B(j+1)=max(0,(1-kap(k+1))*(1+R*B(j))-kap(k+1)*hb(k+1));
end
fprintf('r=%.2f  age j | true assets | floor B_j | ratio | true cons | bound cons | ratio\n',r);
for j=[1 6 11 21 31 41 51 60]
  fprintf('        %6d | %11.3f | %9.3f | %5.2f | %9.4f | %10.4f | %5.2f\n', ...
    j-1,A(j),B(j),B(j)/max(A(j),1e-9),C(j),Cb(j),C(j)/Cb(j));
end
fprintf('\n mean over the life: true assets %.3f, floor %.3f (%.0f%%); demand %.3f\n', ...
  mean(A),mean(B),100*mean(B)/mean(A),alpha/((1-alpha)*(r+delta)));
% (iii) counterfactual: floor recursion using the TRUE mean consumption path
Bt=zeros(J,1);
for j=1:J-1
  Bt(j+1)=max(0,1+R*Bt(j)-C(j));
end
fprintf(' counterfactual with true mean consumption: mean assets %.3f (truth %.3f)\n',mean(Bt),mean(A));
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
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
