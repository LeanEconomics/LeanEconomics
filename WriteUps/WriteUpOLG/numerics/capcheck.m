% Is the artefactual asset cap forward-invariant on the rate interval the crossing needs?
% The policy obeys  a' <= (1-kappa_k)(R a + y_max), so [0,cap] maps into itself only if
% (1-kappa_k) R < 1, i.e. Thorn < 1, i.e. beta R < 1.  Check where that holds.
function capcheck
beta=0.96; gam=3; J=60; ymax=2.98; lam=1/beta-1;
fprintf('lambda = 1/beta - 1 = %.4f\n\n',lam);
fprintf('   r     | betaR  | Thorn  | kappa_59 | (1-k59)R | cap invariant? | min cap that works\n');
for r=[-0.07 -0.04 0 0.02 0.0417 0.05 0.06 0.08 0.10]
  R=1+r; Th=(beta*R)^(1/gam);
  kap=1; for k=1:J-1, kap=kap*R/(Th+kap*R); end
  s=(1-kap)*R;
  if s<1, cm=sprintf('%.1f',(1-kap)*ymax/(1-s)); ok='yes'; else cm='none exists'; ok='NO'; end
  fprintf(' %+.4f | %.4f | %.4f | %8.5f | %8.4f | %14s | %s\n',r,beta*R,Th,kap,s,ok,cm);
end
fprintf('\n the true equilibrium rate is near 5%%, and the provable floor needs about 9%%;\n');
fprintf(' both are above lambda, where no asset cap is forward-invariant.\n');
end
