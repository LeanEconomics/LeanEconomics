% Two questions about the floor at the top of the interval.
% (1) Does the affine intercept F_k(z) go negative? Assets cannot, so a clamp would be valid
%     and the aggregate would inherit the slack.
% (2) In the power-mean recursion, how much of the loss is the saving ceiling rather than the
%     power mean? Re-run it with the TRUE saving, which makes it exact, and with two ceilings.
function floordiag
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; r=0.08;
[Pi,y,nu]=tauchen(rho,sigma,nz); R=1+r; Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
Hr=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
  Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
% (1) the affine intercept by age and state
G=1; F=zeros(nz,1); neg=0; tot=0; minF=inf;
fprintf('(1) affine floor intercept F_k(z): age | F at z_min | F at z_mid | F at z_max | any<0\n');
for k=0:K-1
  Fn=Pi*F + G*((1-kap(k+2))*y - kap(k+2)*H(:,k+2)); G=1+G*(1-kap(k+2))*R; F=Fn;
  neg=neg+sum(F<0); tot=tot+nz; minF=min(minF,min(F));
  if any(k==[0 4 9 29 58])
    fprintf('    %28d | %10.3f | %10.3f | %10.3f | %d\n',k+1,F(1),F(4),F(nz),sum(F<0));
  end
end
fprintf('    negative entries: %d of %d; most negative %.4f\n\n',neg,tot,minF);
% (2) power-mean recursion with three choices of the saving argument
na=300; ag=[0; exp(linspace(log(1e-3),log(400),na-1))'];
m=y'+R*ag; c=egm(R,beta,gam,y,Pi,ag,J);
lab={'true saving','ceiling from riskHumanWealth','arithmetic bound (current)'};
for mode=1:2
  Gam=zeros(na,nz,J); Gam(:,:,1)=m;
  for k=0:K-1
    Ab=zeros(na,nz);
    for z=1:nz
      if mode==1, Ab(:,z)=m(:,z)-c{k+2}(:,z);
      else, Ab(:,z)=max(0,(1-kap(k+2))*m(:,z)-kap(k+2)*Hr(z,k+2)); end
    end
    Gn=zeros(na,nz);
    for z=1:nz
      Gk=zeros(na,nz);
      for w=1:nz
        Gk(:,w)=interp1(ag,Gam(:,w,k+1),min(max(Ab(:,z),ag(1)),ag(end)),'linear','extrap');
      end
      Mz=(sum(Pi(z,:).*(Gk.^(-gam)),2)).^(-1/gam);
      Gn(:,z)=min(m(:,z),Mz/Th);
    end
    Gam(:,:,k+2)=Gn;
  end
  fprintf('(2) %-30s : bound at birth %.4f\n',lab{mode},nu'*Gam(1,:,J)');
end
fprintf('(2) %-30s : bound at birth %.4f\n',lab{3},nu'*(kap(J)*(m(1,:)'+H(:,J))));
fprintf('    truth at birth %.4f\n',nu'*c{J}(1,:)');
% how loose is the one-step saving ceiling at birth?
Ab=max(0,(1-kap(J))*m(1,:)'-kap(J)*Hr(:,J)); At=m(1,:)'-c{J}(1,:)';
fprintf('    one-step saving at birth: true %.4f, ceiling %.4f (%.2fx)\n', ...
  nu'*At,nu'*Ab,(nu'*Ab)/(nu'*At));
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
