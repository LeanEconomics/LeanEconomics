% Chaining the two Euler equations through the CERTAINTY EQUIVALENT rather than the minimum.
%   c2^-g >= bR2 M(C2(.,b2))^-g   (Euler under the cap at R2)
%   c1^-g <= bR1 M(C1(.,b1))^-g   (Euler above the floor at R1)
%  =>  c2/c1 <= (R1/R2)^(1/g) * M(C2(.,b2)) / M(C1(.,b1)) .
% Propagating a CONSTANT shift through M costs the gradient sum
%   A = sum_z' pi (C1(z',b1)/M)^(-g-1)     (=1 iff next period's consumption is riskless),
% which is the per-stage multiplier of THIS formulation.  Compare 4.7 for the min-based one.
function cestep
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06;
fprintf(' gam | q=(R1/R2)^(1/g) | max A (CE mult) | A^59   | min-based mult | q*A\n');
for gam=[1 2 3 5 8]
  R1=1+r1; q=(R1/(1+r2))^(1/gam);
  c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
  Amax=0; Bmax=0;
  for k=1:J-1
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0); c1=c1f{k+1}(:,z);
      for i=1:5:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        w=Pi(z,:)';
        M=(w'*(Cn.^(-gam)))^(-1/gam);
        A=w'*((Cn/M).^(-gam-1));
        Amax=max(Amax,A);
        Bmax=max(Bmax,c1(i)*q/min(Cn));
      end
    end
  end
  fprintf(' %3g | %15.6f | %15.4f | %6.2e | %14.2f | %.4f\n',...
          gam,q,Amax,Amax^59,Bmax,q*Amax);
end
fprintf('\n the CE formulation contracts iff q*A <= 1.\n');
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
