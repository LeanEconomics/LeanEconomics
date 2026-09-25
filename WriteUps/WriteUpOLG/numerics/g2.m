% Theorem 1 at (a=0,z) across [r1,r2] is exactly c0(R2) <= c0(R1).  Sandwich it:
%   ceiling at R2 : kap2_k (y + Harith2_k(z))          [LifeCycle upper sandwich]
%   floor   at R1 : kap1_k (y + Hrisk1_k(z))           [Incidence, power mean -gamma, capped]
% If ceiling(R2) <= floor(R1) the theorem follows with no CE machinery at all.
function g2
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
ag=[0; exp(linspace(log(1e-4),log(600),2999))'];
r1=0.04; r2=0.06;
fprintf(' gam |  floor(R1)  ceil(R2) | true c0(R1) c0(R2) | ceil<=floor | floor/true ceil/true\n');
for gam=[1 1.5 2 2.5 3]
  [F1,~]=bounds(1+r1,beta,gam,y,Pi,J,nz);
  [~,C2]=bounds(1+r2,beta,gam,y,Pi,J,nz);
  c=egm(1+r1,beta,gam,y,Pi,ag,J); t1=c{J}(1,nz);
  c=egm(1+r2,beta,gam,y,Pi,ag,J); t2=c{J}(1,nz);
  if C2<=F1, vd='YES'; else, vd=' no'; end
  fprintf(' %4.2f | %10.5f %9.5f | %10.5f %7.5f |     %s     | %8.3f %8.3f\n',...
          gam,F1,C2,t1,t2,vd,F1/t1,C2/t2);
end
fprintf('\n a ceiling at R2 below the floor at R1 proves Theorem 1 at the state outright.\n');
fprintf(' ceil/true near 1 from above and floor/true near 1 from below is what is needed;\n');
fprintf(' the gap to close is ceil(R2) - floor(R1) against the true c0(R1) - c0(R2).\n');
for gam=[2]
  [F1,~]=bounds(1+r1,beta,gam,y,Pi,J,nz);
  [~,C2]=bounds(1+r2,beta,gam,y,Pi,J,nz);
  c=egm(1+r1,beta,gam,y,Pi,ag,J); t1=c{J}(1,nz);
  c=egm(1+r2,beta,gam,y,Pi,ag,J); t2=c{J}(1,nz);
  fprintf('   gamma=2 : need ceil(R2)-floor(R1) <= 0 ; have %+.5f ; true c0(R1)-c0(R2) = %+.5f\n',...
          C2-F1,t1-t2);
  fprintf('             slack lost above: %.5f (ceiling) + %.5f (floor) = %.5f\n',...
          C2-t2,t1-F1,(C2-t2)+(t1-F1));
end
end
function [F,C]=bounds(R,beta,gam,y,Pi,J,nz)
Th=(beta*R)^(1/gam); kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Ha=zeros(nz,1); Hr=zeros(nz,1);
for k=1:J-1
  Ha=(Pi*(y+Ha))/R;
  x=y+Hr; pm=zeros(nz,1);
  for z=1:nz
    w=Pi(z,:)'; pm(z)=(w'*(x.^(-gam)))^(-1/gam);
  end
  Hr=min(pm/R,(1/kap(k+1)-1)*y);
end
F=kap(J)*(y(nz)+Hr(nz)); C=kap(J)*(y(nz)+Ha(nz));
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
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
