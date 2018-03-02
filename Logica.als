module permissoes

--	Nome melhor para Entidade? (seria um arquivo OU diretorio)
abstract sig Entidade {
	paraTodos: one ParaTodos,
	usuarioExterno: one UsuarioExterno,
	usuarioLocal : one UsuarioLocal
}

sig Diretorio extends Entidade {
--	[Duvida] Diretorio pode ser vazio???
	conteudo: set Entidade
}

sig Arquivo extends Entidade {}

pred root [dir:Diretorio] {
	no dir.~conteudo
}

pred ehCategoriaDe[cat:CategoriaUsuario, ent:Entidade] {
	(cat in ent.paraTodos) or (cat in ent.usuarioExterno) or (cat in ent.usuarioLocal)
}

fact estruturaDeArvore {
	-- nenhum diretorio é ancestral dele mesmo
	no dir: Diretorio | dir in dir.^conteudo

	-- todo arquivo possui um ancestral imediato
	all arq: Arquivo | one arq.~conteudo

	-- todo diretório possui um ou nenhum ancestral imediato
	all dir: Diretorio | lone dir.~conteudo

	-- apenas um diretorio nao possui ancestral imediato (root)
	one dir: Diretorio | root[dir]
}

abstract sig CategoriaUsuario {
	permissao: one Permissao
} {
	-- Toda categoria possui apenas um ancestral
	one ent: Entidade | ehCategoriaDe[this, ent]
}

sig ParaTodos, UsuarioExterno, UsuarioLocal extends CategoriaUsuario {}

abstract sig Permissao {}
	-- Funciona como um enum
one sig Leitura, LeituraEscrita, Dono extends Permissao {}

pred show[]{}
run show for 12
